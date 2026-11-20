import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

namespace Formalism.HermitianLatticeCounting.P

section homRestrict

open Module

/- English proof (translation)
Use `set T := LinearMap.range (g ∘ₗ f) with hT`. Establish `hTS : T ≤ LinearMap.range g`. Rewrite using `[hT, LinearMap.range_comp]`. Conclude with `LinearMap.map_le_range`. Rewrite using `[← Submodule.card_quotient_mul_card_quotient (LinearMap.range g) T hTS]`.

Use `congr 1`. Set `h : B →ₗ[R] C ⧸ T` to `T.mkQ ∘ₗ g`. Establish `hker : LinearMap.ker h = LinearMap.range f`. Use extensionality with `x`. Simplify using `only [h, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, hg ha⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a, rfl⟩`.

Establish `hrange : LinearMap.range h = (LinearMap.range g).map T.mkQ` using `LinearMap.range_comp _ _`. Conclude with `Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans h.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ hrange)).symm.toEquiv`.
-/
lemma s5b7_card_comp {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Injective g) :
    Nat.card (C ⧸ LinearMap.range (g ∘ₗ f)) =
      Nat.card (B ⧸ LinearMap.range f) * Nat.card (C ⧸ LinearMap.range g) := by
  set T := LinearMap.range (g ∘ₗ f) with hT
  have hTS : T ≤ LinearMap.range g := by
    rw [hT, LinearMap.range_comp]; exact LinearMap.map_le_range
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range g) T hTS]
  congr 1
  let h : B →ₗ[R] C ⧸ T := T.mkQ ∘ₗ g
  have hker : LinearMap.ker h = LinearMap.range f := by
    ext x
    simp only [h, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hT, LinearMap.mem_range]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, hg ha⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  have hrange : LinearMap.range h = (LinearMap.range g).map T.mkQ := LinearMap.range_comp _ _
  exact Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans h.quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ hrange)).symm.toEquiv

variable {O : Type} [CommRing O] [IsDedekindDomain O]

/- English proof (translation)
Establish `: Module.FinitePresentation O Y` using `Module.finitePresentation_of_finite O Y`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
lemma s5b7_proj (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
    [Module.IsTorsionFree O Y] : Module.Projective O Y := by
  have : Module.FinitePresentation O Y := Module.finitePresentation_of_finite O Y
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Set `: Field (O ⧸ p)` to `Ideal.Quotient.field p`. Establish `: Module.Finite (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y))` using `Module.Finite.of_restrictScalars_finite O _ _`. Establish `hfin : Finite (Y ⧸ p • (⊤ : Submodule O Y))` using `Module.finite_of_finite (O ⧸ p)`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.natCard_eq_pow_finrank (K := O ⧸ p) (V := Y ⧸ p • (⊤ : Submodule O Y))]`.

Apply `Nat.pow_le_pow_right Nat.card_pos` to reduce the goal to its premises. Use `set a := finrank (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y)) with ha`. Set `b` to `Module.finBasis (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y))`. Use `choose y hy using fun i => Submodule.Quotient.mk_surjective _ (b i)`. Use `set N := Submodule.span O (Set.range y) with hN`.

Establish `hsup : ∀ z : Y, ∃ n ∈ N, z - n ∈ p • (⊤ : Submodule O Y)`. Introduce `z`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk z) i)`. Use `⟨∑ i, c i • y i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]`.

Use `conv_lhs => rw [← b.sum_repr (Submodule.Quotient.mk z)]`. Establish `e1 : (Submodule.Quotient.mk (∑ i, c i • y i) : Y ⧸ p • (⊤ : Submodule O Y)) = ∑ i, Submodule.Quotient.mk (c i • y i)` using `map_sum (Submodule.mkQ (p • ⊤)) _ _`. Rewrite using `[e1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.mk_smul, hy, ← hc]`.

Both sides reduce to the same expression. Establish `htop : (⊤ : Submodule O (Y ⧸ N)) ≤ p • (⊤ : Submodule O (Y ⧸ N))`. Introduce `q _`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨n, hn, hz⟩` from `hsup z`.

Establish `h1 : (Submodule.Quotient.mk z : Y ⧸ N) = N.mkQ (z - n)`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero N).mpr hn, sub_zero]`. Rewrite using `[h1]`. Establish `h2 : (p • (⊤ : Submodule O Y)).map N.mkQ ≤ p • (⊤ : Submodule O (Y ⧸ N))`. Rewrite using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `h2 ⟨_, hz, rfl⟩`. Take `⟨s, hs1, hs⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p (⊤ : Submodule O (Y ⧸ N)) Module.Finite.fg_top htop`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`.

Apply `hp.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using p.neg_mem hs1`. Establish `hsN : ∀ z : Y, s • z ∈ N`. Introduce `z`.

Use `hs (Submodule.Quotient.mk z) trivial` as an intermediate fact. Rewrite `this` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Set `F : Y →ₗ[O] N` to `(LinearMap.lsmul O Y s).codRestrict N hsN`. Establish `hF : Function.Injective F`. Introduce `u v huv`.

Establish `: s • u = s • v` using `congrArg Subtype.val huv`. Conclude with `(smul_right_injective Y hs0) this`. Establish `: IsNoetherian O Y` using `isNoetherian_of_isNoetherianRing_of_finite O Y`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma s5b7_quot_ge (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.IsTorsionFree O Y] :
    Finite (Y ⧸ p • (⊤ : Submodule O Y)) ∧
    Nat.card (O ⧸ p) ^ finrank O Y ≤ Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) := by
  classical
  let : Field (O ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hfin : Finite (Y ⧸ p • (⊤ : Submodule O Y)) := Module.finite_of_finite (O ⧸ p)
  refine ⟨hfin, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := O ⧸ p) (V := Y ⧸ p • (⊤ : Submodule O Y))]
  apply Nat.pow_le_pow_right Nat.card_pos
  set a := finrank (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y)) with ha
  let b := Module.finBasis (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y))
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (b i)
  set N := Submodule.span O (Set.range y) with hN
  have hsup : ∀ z : Y, ∃ n ∈ N, z - n ∈ p • (⊤ : Submodule O Y) := by
    intro z
    choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk z) i)
    refine ⟨∑ i, c i • y i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (Submodule.Quotient.mk z)]
    have e1 : (Submodule.Quotient.mk (∑ i, c i • y i) : Y ⧸ p • (⊤ : Submodule O Y)) =
        ∑ i, Submodule.Quotient.mk (c i • y i) := map_sum (Submodule.mkQ (p • ⊤)) _ _
    rw [e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.Quotient.mk_smul, hy, ← hc]
    rfl
  have htop : (⊤ : Submodule O (Y ⧸ N)) ≤ p • (⊤ : Submodule O (Y ⧸ N)) := by
    intro q _
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨n, hn, hz⟩ := hsup z
    have h1 : (Submodule.Quotient.mk z : Y ⧸ N) = N.mkQ (z - n) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero N).mpr hn,
        sub_zero]
    rw [h1]
    have h2 : (p • (⊤ : Submodule O Y)).map N.mkQ ≤ p • (⊤ : Submodule O (Y ⧸ N)) := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact h2 ⟨_, hz, rfl⟩
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p
    (⊤ : Submodule O (Y ⧸ N)) Module.Finite.fg_top htop
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using p.neg_mem hs1
  have hsN : ∀ z : Y, s • z ∈ N := by
    intro z
    have := hs (Submodule.Quotient.mk z) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  let F : Y →ₗ[O] N := (LinearMap.lsmul O Y s).codRestrict N hsN
  have hF : Function.Injective F := by
    intro u v huv
    have : s • u = s • v := congrArg Subtype.val huv
    exact (smul_right_injective Y hs0) this
  have : IsNoetherian O Y := isNoetherian_of_isNoetherianRing_of_finite O Y
  calc finrank O Y ≤ finrank O N := LinearMap.finrank_le_finrank_of_injective hF
    _ ≤ Fintype.card (Fin a) := finrank_range_le_card y
    _ = a := Fintype.card_fin a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ I) hx (fun r hr z _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Conclude with `I.mul_mem_right _ hr`. Conclude with `I.add_mem (ha i) (hb i)`.

Introduce `hx`. Rewrite using `[pi_eq_sum_univ x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem_smul (hx i) trivial`.
-/
lemma s5b7_smul_top_pi {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (x : Fin n → R) :
    x ∈ I • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ I) hx (fun r hr z _ i => ?_)
      (fun a b ha hb i => ?_)
    · exact I.mul_mem_right _ hr
    · exact I.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (hx i) trivial

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Establish `: (I • (⊤ : Submodule R (M × N))).map (LinearMap.fst R M N) ≤ I • ⊤`. Rewrite using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `this ⟨x, hx, rfl⟩`. Establish `: (I • (⊤ : Submodule R (M × N))).map (LinearMap.snd R M N) ≤ I • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.

Conclude with `this ⟨x, hx, rfl⟩`. Introduce and unpack `⟨a, b⟩ ⟨ha, hb⟩`. Establish `h1 : (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N) ≤ I • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.

Establish `h2 : (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N) ≤ I • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Establish `e : ((a, b) : M × N) = LinearMap.inl R M N a + LinearMap.inr R M N b` using `by simp`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (h1 ⟨a, ha, rfl⟩) (h2 ⟨b, hb, rfl⟩)`.
-/
lemma s5b7_smul_top_prod {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      (I • (⊤ : Submodule R M)).prod (I • (⊤ : Submodule R N)) := by
  apply le_antisymm
  · intro x hx
    constructor
    · have : (I • (⊤ : Submodule R (M × N))).map (LinearMap.fst R M N) ≤ I • ⊤ := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this ⟨x, hx, rfl⟩
    · have : (I • (⊤ : Submodule R (M × N))).map (LinearMap.snd R M N) ≤ I • ⊤ := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this ⟨x, hx, rfl⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have h1 : (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    have h2 : (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    have e : ((a, b) : M × N) = LinearMap.inl R M N a + LinearMap.inr R M N b := by simp
    rw [e]
    exact Submodule.add_mem _ (h1 ⟨a, ha, rfl⟩) (h2 ⟨b, hb, rfl⟩)

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' O Y`. Take `⟨h, hh⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Establish `hfh : ∀ x, f (h x) = x` using `fun x => by`. Use `congrArg (fun g => g x) hh` as an intermediate fact. Simplify using `using this`.

Use `set Q := LinearMap.ker f with hQ`. Establish `: IsNoetherian O (Fin n → O)` using `isNoetherian_of_isNoetherianRing_of_finite _ _`. Set `φ : (Fin n → O) →ₗ[O] Y × Q` to `f.prod ((LinearMap.id - h ∘ₗ f).codRestrict Q (fun x => by`. Rewrite using `[hQ, LinearMap.mem_ker]`. Simplify using `[hfh]))`.

Set `ψ : Y × Q →ₗ[O] (Fin n → O)` to `h.coprod Q.subtype`. Set `e : (Fin n → O) ≃ₗ[O] Y × Q` to `LinearEquiv.ofLinearMap φ ψ (by`. Use extensionality with `x`. Simplify using `[φ, ψ, hfh]`. Simplify using `[φ, ψ, hfh]`.

Establish `: f (x : Fin n → O) = 0` using `x.2`. Simplify using `[φ, ψ, this]`. Establish `: f (x : Fin n → O) = 0` using `x.2`. Simplify using `[φ, ψ, this])`. Use the proof step `(by`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `[φ, ψ])`. Take `⟨fY, aY⟩` from `s5b7_quot_ge p Y`. Take `⟨fQ, aQ⟩` from `s5b7_quot_ge p Q`.

Establish `hrank : finrank O Y + finrank O Q = n`. Use `Submodule.finrank_quotient_add_finrank Q` as an intermediate fact. Rewrite `this` using `[(LinearMap.quotKerEquivOfSurjective f hf).finrank_eq]`. Simplify using `using this`. Establish `hF : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index = Nat.card (O ⧸ p) ^ n`.

Establish `: (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup = AddSubgroup.pi Set.univ fun _ : Fin n => (Submodule.toAddSubgroup p)`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, s5b7_smul_top_pi, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]`. Rewrite using `[this, AddSubgroup.index_pi]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Use `congr 1`. Establish `hPQ : (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index = (p • (⊤ : Submodule O Y)).toAddSubgroup.index * (p • (⊤ : Submodule O Q)).toAddSubgroup.index`. Rewrite using `[s5b7_smul_top_prod, ← AddSubgroup.index_prod]`. Both sides reduce to the same expression. Establish `hE : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index = (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index`.

Establish `hm : (p • (⊤ : Submodule O (Fin n → O))).map (e : (Fin n → O) →ₗ[O] Y × Q) = p • (⊤ : Submodule O (Y × Q))`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]`. Conclude with `Nat.card_congr (Submodule.Quotient.equiv _ _ e hm).toEquiv`. Express the relevant statement in the definitionally equal form `(p • (⊤ : Submodule O Y)).toAddSubgroup.index = _`. Express the relevant statement in the definitionally equal form `_ ≤ (p • (⊤ : Submodule O Y)).toAddSubgroup.index at aY`.

Express the relevant statement in the definitionally equal form `_ ≤ (p • (⊤ : Submodule O Q)).toAddSubgroup.index at aQ`. Use `set a := (p • (⊤ : Submodule O Y)).toAddSubgroup.index with ha`. Use `set b := (p • (⊤ : Submodule O Q)).toAddSubgroup.index with hb`. Use `set k := Nat.card (O ⧸ p) with hk`. Establish `hk0 : 0 < k` using `Nat.card_pos`.

Establish `hab : a * b = k ^ finrank O Y * k ^ finrank O Q`. Rewrite using `[← hPQ, ← hE, hF, ← pow_add, hrank]`. Assume the negation of the conclusion as `hne`. Establish `hlt : k ^ finrank O Y < a` using `lt_of_le_of_ne aY (Ne.symm hne)`. Establish `hpos : 0 < k ^ finrank O Q` using `pow_pos hk0 _`.

Establish `: k ^ finrank O Y * k ^ finrank O Q < a * b`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers.
-/
theorem s5b7_quot (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) = Nat.card (O ⧸ p) ^ finrank O Y := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O Y
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfh : ∀ x, f (h x) = x := fun x => by
    have := congrArg (fun g => g x) hh; simpa using this
  set Q := LinearMap.ker f with hQ
  have : IsNoetherian O (Fin n → O) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let φ : (Fin n → O) →ₗ[O] Y × Q :=
    f.prod ((LinearMap.id - h ∘ₗ f).codRestrict Q (fun x => by
      rw [hQ, LinearMap.mem_ker]; simp [hfh]))
  let ψ : Y × Q →ₗ[O] (Fin n → O) := h.coprod Q.subtype
  let e : (Fin n → O) ≃ₗ[O] Y × Q := LinearEquiv.ofLinearMap φ ψ
    (by
      ext x
      · simp [φ, ψ, hfh]
      · simp [φ, ψ, hfh]
      · have : f (x : Fin n → O) = 0 := x.2
        simp [φ, ψ, this]
      · have : f (x : Fin n → O) = 0 := x.2
        simp [φ, ψ, this])
    (by
      apply LinearMap.ext; intro x
      simp [φ, ψ])
  obtain ⟨fY, aY⟩ := s5b7_quot_ge p Y
  obtain ⟨fQ, aQ⟩ := s5b7_quot_ge p Q
  have hrank : finrank O Y + finrank O Q = n := by
    have := Submodule.finrank_quotient_add_finrank Q
    rw [(LinearMap.quotKerEquivOfSurjective f hf).finrank_eq] at this
    simpa using this
  have hF : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index = Nat.card (O ⧸ p) ^ n := by
    have : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup =
        AddSubgroup.pi Set.univ fun _ : Fin n => (Submodule.toAddSubgroup p) := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, s5b7_smul_top_pi, AddSubgroup.mem_pi, Set.mem_univ,
        forall_true_left]
    rw [this, AddSubgroup.index_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
  have hPQ : (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index =
      (p • (⊤ : Submodule O Y)).toAddSubgroup.index *
        (p • (⊤ : Submodule O Q)).toAddSubgroup.index := by
    rw [s5b7_smul_top_prod, ← AddSubgroup.index_prod]
    rfl
  have hE : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index =
      (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index := by
    have hm : (p • (⊤ : Submodule O (Fin n → O))).map (e : (Fin n → O) →ₗ[O] Y × Q) =
        p • (⊤ : Submodule O (Y × Q)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    exact Nat.card_congr (Submodule.Quotient.equiv _ _ e hm).toEquiv
  change (p • (⊤ : Submodule O Y)).toAddSubgroup.index = _
  change _ ≤ (p • (⊤ : Submodule O Y)).toAddSubgroup.index at aY
  change _ ≤ (p • (⊤ : Submodule O Q)).toAddSubgroup.index at aQ
  set a := (p • (⊤ : Submodule O Y)).toAddSubgroup.index with ha
  set b := (p • (⊤ : Submodule O Q)).toAddSubgroup.index with hb
  set k := Nat.card (O ⧸ p) with hk
  have hk0 : 0 < k := Nat.card_pos
  have hab : a * b = k ^ finrank O Y * k ^ finrank O Q := by
    rw [← hPQ, ← hE, hF, ← pow_add, hrank]
  by_contra hne
  have hlt : k ^ finrank O Y < a := lt_of_le_of_ne aY (Ne.symm hne)
  have hpos : 0 < k ^ finrank O Q := pow_pos hk0 _
  have : k ^ finrank O Y * k ^ finrank O Q < a * b :=
    calc k ^ finrank O Y * k ^ finrank O Q < a * k ^ finrank O Q :=
          Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ a * b := Nat.mul_le_mul_left _ aQ
  omega

/- English proof (translation)
Establish `: Module.Projective O p` using `s5b7_proj p`. Take `⟨t, htp, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp0`. Establish `hcomm : ∀ (ψ : p →ₗ[O] X) (a c : p), (a : O) • ψ c = (c : O) • ψ a`. Introduce `ψ a c`. Rewrite using `[← map_smul, ← map_smul]`.

Use `congr 1`. Use `ext`. Simplify using `[mul_comm]`. Establish `htf : Module.IsTorsionFree O (p →ₗ[O] X)` using `inferInstance`. Establish `: Module.Projective O (p →ₗ[O] X)` using `s5b7_proj _`.

Establish `hrange : LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p)) = p • (⊤ : Submodule O (p →ₗ[O] X))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨ψ, rfl⟩`. Take `⟨n, g, hg⟩` from `Module.Finite.exists_fin' O p`. Take `⟨s, hs⟩` from `Module.projective_lifting_property g LinearMap.id hg`.

Establish `hgs : ∀ c, g (s c) = c` using `fun c => by`. Use `congrArg (fun u => u c) hs` as an intermediate fact. Simplify using `using this`. Establish `key : LinearMap.lcomp O X (Submodule.subtype p) ψ = ∑ i, ((g (fun j => if i = j then 1 else 0) : p) : O) • ((LinearMap.toSpanSingleton O X (ψ 1)) ∘ₗ (LinearMap.proj i) ∘ₗ s)`. Use extensionality with `c`.

Establish `h1 : (c : O) = ∑ i, s c i * ((g (fun j => if i = j then 1 else 0) : p) : O)` using `by conv_lhs => rw [← hgs c, pi_eq_sum_univ (s c)]`. Simplify using `[map_sum]`. Simplify using `only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]`. Establish `h2 : ψ (c : O) = (c : O) • ψ 1`. Rewrite using `[← map_smul]`.

Simplify using the standard rewrite rules. Rewrite using `[h2, h1, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Rewrite using `[key]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (g _).2 trivial`. Rewrite using `[Submodule.smul_le]`. Introduce `a ha ψ _`. Use `⟨LinearMap.toSpanSingleton O X (ψ ⟨a, ha⟩), ?_⟩` and prove the remaining obligations. Use extensionality with `c`.

Simplify using `using hcomm ψ c ⟨a, ha⟩`. Rewrite using `[hrange, s5b7_quot p (p →ₗ[O] X)]`. Use `congr 1`. Apply `le_antisymm` to reduce the goal to its premises. Set `ev : (p →ₗ[O] X) →ₗ[O] X` to `LinearMap.applyₗ (⟨t, htp⟩ : p)`.

Establish `hev : Function.Injective ev`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `ψ hψ`. Use extensionality with `c`. Establish `h1` using `hcomm ψ ⟨t, htp⟩ c`.

Establish `h2 : ψ ⟨t, htp⟩ = 0` using `hψ`. Rewrite `h1` using `[h2, smul_zero]`. Conclude with `(smul_eq_zero_iff_right ht0).mp h1`. Conclude with `LinearMap.finrank_le_finrank_of_injective hev`. Set `j : X →ₗ[O] (p →ₗ[O] X)` to `(LinearMap.lcomp O X (Submodule.subtype p)) ∘ₗ (LinearMap.ringLmapEquivSelf O O X).symm.toLinearMap`.

Establish `hj : Function.Injective j`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h1 : j x ⟨t, htp⟩ = 0` using `by rw [hx]; rfl`. Establish `h2 : t • x = 0` using `by simpa [j] using h1`.

Conclude with `(smul_eq_zero_iff_right ht0).mp h2`. Conclude with `LinearMap.finrank_le_finrank_of_injective hj`.
-/
theorem s5b7_ideal (p : Ideal O) [hp : p.IsMaximal] (hp0 : p ≠ ⊥) [Finite (O ⧸ p)] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Nat.card ((p →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))) =
      Nat.card (O ⧸ p) ^ finrank O X := by
  classical
  have : Module.Projective O p := s5b7_proj p
  obtain ⟨t, htp, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hcomm : ∀ (ψ : p →ₗ[O] X) (a c : p), (a : O) • ψ c = (c : O) • ψ a := by
    intro ψ a c
    rw [← map_smul, ← map_smul]
    congr 1
    ext
    simp [mul_comm]
  have htf : Module.IsTorsionFree O (p →ₗ[O] X) := inferInstance
  have : Module.Projective O (p →ₗ[O] X) := s5b7_proj _
  have hrange : LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p)) =
      p • (⊤ : Submodule O (p →ₗ[O] X)) := by
    apply le_antisymm
    · rintro _ ⟨ψ, rfl⟩
      obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O p
      obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
      have hgs : ∀ c, g (s c) = c := fun c => by
        have := congrArg (fun u => u c) hs; simpa using this
      have key : LinearMap.lcomp O X (Submodule.subtype p) ψ =
          ∑ i, ((g (fun j => if i = j then 1 else 0) : p) : O) •
            ((LinearMap.toSpanSingleton O X (ψ 1)) ∘ₗ (LinearMap.proj i) ∘ₗ s) := by
        ext c
        have h1 : (c : O) = ∑ i, s c i * ((g (fun j => if i = j then 1 else 0) : p) : O) := by
          conv_lhs => rw [← hgs c, pi_eq_sum_univ (s c)]
          simp [map_sum]
        simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          LinearMap.toSpanSingleton_apply]
        have h2 : ψ (c : O) = (c : O) • ψ 1 := by
          rw [← map_smul]; simp
        rw [h2, h1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
      rw [key]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (g _).2 trivial
    · rw [Submodule.smul_le]
      intro a ha ψ _
      refine ⟨LinearMap.toSpanSingleton O X (ψ ⟨a, ha⟩), ?_⟩
      ext c
      simpa using hcomm ψ c ⟨a, ha⟩
  rw [hrange, s5b7_quot p (p →ₗ[O] X)]
  congr 1
  apply le_antisymm
  · let ev : (p →ₗ[O] X) →ₗ[O] X := LinearMap.applyₗ (⟨t, htp⟩ : p)
    have hev : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      intro ψ hψ
      ext c
      have h1 := hcomm ψ ⟨t, htp⟩ c
      have h2 : ψ ⟨t, htp⟩ = 0 := hψ
      rw [h2, smul_zero] at h1
      exact (smul_eq_zero_iff_right ht0).mp h1
    exact LinearMap.finrank_le_finrank_of_injective hev
  · let j : X →ₗ[O] (p →ₗ[O] X) :=
      (LinearMap.lcomp O X (Submodule.subtype p)) ∘ₗ
        (LinearMap.ringLmapEquivSelf O O X).symm.toLinearMap
    have hj : Function.Injective j := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : j x ⟨t, htp⟩ = 0 := by rw [hx]; rfl
      have h2 : t • x = 0 := by simpa [j] using h1
      exact (smul_eq_zero_iff_right ht0).mp h2
    exact LinearMap.finrank_le_finrank_of_injective hj

/- English proof (translation)
Establish `hsimple : IsSimpleModule O (M ⧸ N)` using `isSimpleModule_iff_isCoatom.mpr hN`. Take `⟨p, hp, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hsimple`. Establish `hp0 : p ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hp hO`. Establish `: Finite (O ⧸ p)` using `Finite.of_equiv _ e.toEquiv`. Set `π : M →ₗ[O] O ⧸ p` to `e.toLinearMap ∘ₗ N.mkQ`.

Establish `hπs : Function.Surjective π` using `e.surjective.comp (Submodule.mkQ_surjective N)`. Establish `hπN : ∀ m, π m = 0 ↔ m ∈ N`. Introduce `m`. Simplify using `[π]`. Take `⟨l, hl⟩` from `Module.projective_lifting_property (Submodule.mkQ p) π (Submodule.mkQ_surjective p)`.

Establish `hl' : ∀ m, Submodule.Quotient.mk (l m) = π m` using `fun m => by`. Use `congrArg (fun u => u m) hl` as an intermediate fact. Simplify using `using this`. Take `⟨x, hx⟩` from `hπs (Submodule.Quotient.mk 1)`. Establish `hlp : ∀ m, l m ∈ p ↔ m ∈ N`.

Introduce `m`. Rewrite using `[← hπN, ← hl', Submodule.Quotient.mk_eq_zero]`. Establish `hax : ∀ a : O, π (a • x) = Submodule.Quotient.mk a`. Introduce `a`. Rewrite using `[map_smul, hx, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]`.

Establish `hpx : ∀ a : p, (a : O) • x ∈ N`. Introduce `a`. Rewrite using `[← hπN, hax, Submodule.Quotient.mk_eq_zero]`. Conclude with `a.2`. Set `j : p →ₗ[O] N` to `((LinearMap.toSpanSingleton O M x) ∘ₗ p.subtype).codRestrict N hpx`.

Establish `hj : ∀ a : p, ((j a : N) : M) = (a : O) • x` using `fun a => rfl`. Set `R` to `LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))`. Set `Θ : (N →ₗ[O] X) →ₗ[O] (p →ₗ[O] X) ⧸ R` to `R.mkQ ∘ₗ LinearMap.lcomp O X j`. Establish `hres : ∀ m : M, m - l m • x ∈ N`. Introduce `m`.

Rewrite using `[← hπN, map_sub, hax, hl', sub_self]`. Establish `hker : LinearMap.ker Θ = LinearMap.range (LinearMap.lcomp O X N.subtype)`. Use extensionality with `φ`. Simplify using `only [Θ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, R, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨ψ, hψ⟩`. Set `ρ : M →ₗ[O] N` to `(LinearMap.id - (LinearMap.toSpanSingleton O M x) ∘ₗ l).codRestrict N hres`. Use `⟨φ ∘ₗ ρ + ψ ∘ₗ l, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Establish `h1 : ψ (l (m : M)) = φ (j ⟨l (m : M), (hlp _).mpr m.2⟩)`.

Use `congrArg (fun u => u ⟨l (m : M), (hlp _).mpr m.2⟩) hψ` as an intermediate fact. Simplify using `using this`. Establish `h2 : ρ (m : M) + j ⟨l (m : M), (hlp _).mpr m.2⟩ = m`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((m : M) - l (m : M) • x) + l (m : M) • x = m`.

Conclude with `sub_add_cancel _ _`. Simplify using `only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.add_apply, LinearMap.comp_apply]`. Rewrite using `[h1, ← map_add, h2]`. Introduce and unpack `⟨Φ, rfl⟩`. Use `⟨LinearMap.toSpanSingleton O X (Φ x), ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Simplify using `[hj]`. Establish `hsurj : Function.Surjective Θ`. Introduce `q`. Take `⟨ψ, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Set `lN : N →ₗ[O] p` to `(l ∘ₗ N.subtype).codRestrict p (fun m => (hlp _).mpr m.2)`. Use `⟨ψ ∘ₗ lN, ?_⟩` and prove the remaining obligations. Simplify using `only [Θ, LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Establish `ht : l x - 1 ∈ p`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hl', hx, sub_self]`. Use `⟨LinearMap.toSpanSingleton O X (ψ ⟨l x - 1, ht⟩), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Establish `h3 : lN (j a) = a + (a : O) • (⟨l x - 1, ht⟩ : p)`. Use `ext`.

Simplify using `[lN, hj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply, LinearMap.sub_apply, LinearMap.comp_apply]`. Rewrite using `[h3, map_add, map_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← hker, Nat.card_congr (LinearMap.quotKerEquivOfSurjective Θ hsurj).toEquiv, s5b7_ideal p hp0 X, Nat.card_congr e.toEquiv]`.
-/
theorem s5b7_step (hO : ¬ IsField O) (M X : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (N : Submodule O M) (hN : IsCoatom N) [Finite (M ⧸ N)] :
    Nat.card ((N →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X N.subtype)) =
      Nat.card (M ⧸ N) ^ finrank O X := by
  classical
  have hsimple : IsSimpleModule O (M ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp hO
  have : Finite (O ⧸ p) := Finite.of_equiv _ e.toEquiv
  let π : M →ₗ[O] O ⧸ p := e.toLinearMap ∘ₗ N.mkQ
  have hπs : Function.Surjective π := e.surjective.comp (Submodule.mkQ_surjective N)
  have hπN : ∀ m, π m = 0 ↔ m ∈ N := by
    intro m
    simp [π]
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Submodule.mkQ p) π
    (Submodule.mkQ_surjective p)
  have hl' : ∀ m, Submodule.Quotient.mk (l m) = π m := fun m => by
    have := congrArg (fun u => u m) hl; simpa using this
  obtain ⟨x, hx⟩ := hπs (Submodule.Quotient.mk 1)
  have hlp : ∀ m, l m ∈ p ↔ m ∈ N := by
    intro m
    rw [← hπN, ← hl', Submodule.Quotient.mk_eq_zero]
  have hax : ∀ a : O, π (a • x) = Submodule.Quotient.mk a := by
    intro a
    rw [map_smul, hx, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  have hpx : ∀ a : p, (a : O) • x ∈ N := by
    intro a
    rw [← hπN, hax, Submodule.Quotient.mk_eq_zero]
    exact a.2
  let j : p →ₗ[O] N := ((LinearMap.toSpanSingleton O M x) ∘ₗ p.subtype).codRestrict N hpx
  have hj : ∀ a : p, ((j a : N) : M) = (a : O) • x := fun a => rfl
  let R := LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))
  let Θ : (N →ₗ[O] X) →ₗ[O] (p →ₗ[O] X) ⧸ R := R.mkQ ∘ₗ LinearMap.lcomp O X j
  have hres : ∀ m : M, m - l m • x ∈ N := by
    intro m
    rw [← hπN, map_sub, hax, hl', sub_self]
  have hker : LinearMap.ker Θ = LinearMap.range (LinearMap.lcomp O X N.subtype) := by
    ext φ
    simp only [Θ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, R, LinearMap.mem_range]
    constructor
    · rintro ⟨ψ, hψ⟩
      let ρ : M →ₗ[O] N :=
        (LinearMap.id - (LinearMap.toSpanSingleton O M x) ∘ₗ l).codRestrict N hres
      refine ⟨φ ∘ₗ ρ + ψ ∘ₗ l, ?_⟩
      ext m
      have h1 : ψ (l (m : M)) = φ (j ⟨l (m : M), (hlp _).mpr m.2⟩) := by
        have := congrArg (fun u => u ⟨l (m : M), (hlp _).mpr m.2⟩) hψ
        simpa using this
      have h2 : ρ (m : M) + j ⟨l (m : M), (hlp _).mpr m.2⟩ = m := by
        apply Subtype.ext
        change ((m : M) - l (m : M) • x) + l (m : M) • x = m
        exact sub_add_cancel _ _
      simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.add_apply,
        LinearMap.comp_apply]
      rw [h1, ← map_add, h2]
    · rintro ⟨Φ, rfl⟩
      refine ⟨LinearMap.toSpanSingleton O X (Φ x), ?_⟩
      ext a
      simp [hj]
  have hsurj : Function.Surjective Θ := by
    intro q
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let lN : N →ₗ[O] p := (l ∘ₗ N.subtype).codRestrict p (fun m => (hlp _).mpr m.2)
    refine ⟨ψ ∘ₗ lN, ?_⟩
    simp only [Θ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have ht : l x - 1 ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hl', hx, sub_self]
    refine ⟨LinearMap.toSpanSingleton O X (ψ ⟨l x - 1, ht⟩), ?_⟩
    ext a
    have h3 : lN (j a) = a + (a : O) • (⟨l x - 1, ht⟩ : p) := by
      ext
      simp [lN, hj]
      ring
    simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      LinearMap.sub_apply, LinearMap.comp_apply]
    rw [h3, map_add, map_smul]
    abel
  rw [← hker, Nat.card_congr (LinearMap.quotKerEquivOfSurjective Θ hsurj).toEquiv,
    s5b7_ideal p hp0 X, Nat.card_congr e.toEquiv]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `P M _ _ _ _ _ _ ι hι hn0 hn`. Establish `hinf : Infinite O`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_infinite_iff_finite]`. Conclude with `hO (Finite.isField_of_domain O)`. Break down `eq_top_or_exists_le_coatom (LinearMap.range ι) with htop | ⟨N, hN, hle⟩` into its components or cases. Establish `h1 : n = 1`.

Rewrite using `[← hn, htop]`. Simplify using the standard rewrite rules. Establish `hs : Function.Surjective ι` using `LinearMap.range_eq_top.mp htop`. Set `e` to `LinearEquiv.ofBijective ι ⟨hι, hs⟩`. Establish `h2 : LinearMap.range (LinearMap.lcomp O X ι) = ⊤`.

Rewrite using `[LinearMap.range_eq_top]`. Introduce `φ`. Use `⟨φ ∘ₗ e.symm.toLinearMap, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Express the relevant statement in the definitionally equal form `φ (e.symm (e y)) = φ y`.

Rewrite using `[e.symm_apply_apply]`. Rewrite using `[h2, h1]`. Simplify using the standard rewrite rules. Set `ι1 : P →ₗ[O] N` to `ι.codRestrict N (fun y => hle ⟨y, rfl⟩)`. Establish `hι1 : Function.Injective ι1` using `fun a b hab => hι (congrArg Subtype.val hab)`.

Establish `hcomp : ι = N.subtype ∘ₗ ι1` using `by ext y; rfl`. Establish `hc` using `s5b7_card_comp ι1 N.subtype N.injective_subtype`. Rewrite `hc` using `[← hcomp, hn, Submodule.range_subtype]`. Establish `hA : Nat.card (N ⧸ LinearMap.range ι1) ≠ 0` using `fun h => hn0 (by rw [hc, h, zero_mul])`. Establish `hB : Nat.card (M ⧸ N) ≠ 0` using `fun h => hn0 (by rw [hc, h, mul_zero])`.

Establish `hfB : Finite (M ⧸ N)` using `Nat.finite_of_card_ne_zero hB`. Establish `hfA : Finite (N ⧸ LinearMap.range ι1)` using `Nat.finite_of_card_ne_zero hA`. Establish `hnt : Nontrivial (M ⧸ N)` using `Submodule.Quotient.nontrivial_iff.mpr hN.1`. Establish `hB2 : 1 < Nat.card (M ⧸ N)` using `Finite.one_lt_card`. Establish `hlt : Nat.card (N ⧸ LinearMap.range ι1) < n`.

Rewrite using `[hc]`. Establish `: 0 < Nat.card (N ⧸ LinearMap.range ι1)` using `Nat.pos_of_ne_zero hA`. Use the polynomial consequences of the given equalities and inequalities. Establish `: IsNoetherian O M` using `isNoetherian_of_isNoetherianRing_of_finite O M`. Establish `: Module.Projective O N` using `s5b7_proj N`.

Establish `h1` using `ih _ hlt P N ι1 hι1 hA rfl`. Establish `h2` using `s5b7_step hO M X N hN`. Establish `hinj : Function.Injective (LinearMap.lcomp O X ι1)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `φ hφ`.

Use extensionality with `y`. Take `⟨a, b, hab, hEq⟩` from `Finite.exists_ne_map_eq_of_infinite (fun a : O => (Submodule.Quotient.mk (a • y) : N ⧸ LinearMap.range ι1))`. Rewrite `hEq` using `[Submodule.Quotient.eq, ← sub_smul]`. Take `⟨z, hz⟩` from `hEq`. Establish `h3 : φ (ι1 z) = 0`.

Use `congrArg (fun u => u z) hφ` as an intermediate fact. Simplify using `using this`. Rewrite `h3` using `[hz, map_smul]`. Conclude with `(smul_eq_zero_iff_right (sub_ne_zero.mpr hab)).mp h3`. Establish `hc2` using `s5b7_card_comp (LinearMap.lcomp O X N.subtype) (LinearMap.lcomp O X ι1) hinj`.

Establish `hcomp2 : LinearMap.lcomp O X ι1 ∘ₗ LinearMap.lcomp O X N.subtype = LinearMap.lcomp O X ι`. Use extensionality with `φ y`. Both sides reduce to the same expression. Rewrite `hc2` using `[hcomp2, h1, h2]`. Rewrite using `[hc2, hc, mul_pow, mul_comm]`.
-/
theorem s5b7_main (hO : ¬ IsField O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] : ∀ (n : ℕ) (P M : Type) [AddCommGroup P] [Module O P] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] (ι : P →ₗ[O] M),
    Function.Injective ι → n ≠ 0 → Nat.card (M ⧸ LinearMap.range ι) = n →
    Nat.card ((P →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X ι)) = n ^ finrank O X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P M _ _ _ _ _ _ ι hι hn0 hn
  classical
  have hinf : Infinite O := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hO (Finite.isField_of_domain O)
  rcases eq_top_or_exists_le_coatom (LinearMap.range ι) with htop | ⟨N, hN, hle⟩
  · have h1 : n = 1 := by
      rw [← hn, htop]; simp
    have hs : Function.Surjective ι := LinearMap.range_eq_top.mp htop
    let e := LinearEquiv.ofBijective ι ⟨hι, hs⟩
    have h2 : LinearMap.range (LinearMap.lcomp O X ι) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro φ
      refine ⟨φ ∘ₗ e.symm.toLinearMap, ?_⟩
      ext y
      change φ (e.symm (e y)) = φ y
      rw [e.symm_apply_apply]
    rw [h2, h1]; simp
  · let ι1 : P →ₗ[O] N := ι.codRestrict N (fun y => hle ⟨y, rfl⟩)
    have hι1 : Function.Injective ι1 := fun a b hab => hι (congrArg Subtype.val hab)
    have hcomp : ι = N.subtype ∘ₗ ι1 := by ext y; rfl
    have hc := s5b7_card_comp ι1 N.subtype N.injective_subtype
    rw [← hcomp, hn, Submodule.range_subtype] at hc
    have hA : Nat.card (N ⧸ LinearMap.range ι1) ≠ 0 := fun h => hn0 (by rw [hc, h, zero_mul])
    have hB : Nat.card (M ⧸ N) ≠ 0 := fun h => hn0 (by rw [hc, h, mul_zero])
    have hfB : Finite (M ⧸ N) := Nat.finite_of_card_ne_zero hB
    have hfA : Finite (N ⧸ LinearMap.range ι1) := Nat.finite_of_card_ne_zero hA
    have hnt : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hN.1
    have hB2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hlt : Nat.card (N ⧸ LinearMap.range ι1) < n := by
      rw [hc]
      have : 0 < Nat.card (N ⧸ LinearMap.range ι1) := Nat.pos_of_ne_zero hA
      nlinarith
    have : IsNoetherian O M := isNoetherian_of_isNoetherianRing_of_finite O M
    have : Module.Projective O N := s5b7_proj N
    have h1 := ih _ hlt P N ι1 hι1 hA rfl
    have h2 := s5b7_step hO M X N hN
    have hinj : Function.Injective (LinearMap.lcomp O X ι1) := by
      rw [injective_iff_map_eq_zero]
      intro φ hφ
      ext y
      obtain ⟨a, b, hab, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
        (fun a : O => (Submodule.Quotient.mk (a • y) : N ⧸ LinearMap.range ι1))
      rw [Submodule.Quotient.eq, ← sub_smul] at hEq
      obtain ⟨z, hz⟩ := hEq
      have h3 : φ (ι1 z) = 0 := by
        have := congrArg (fun u => u z) hφ
        simpa using this
      rw [hz, map_smul] at h3
      exact (smul_eq_zero_iff_right (sub_ne_zero.mpr hab)).mp h3
    have hc2 := s5b7_card_comp (LinearMap.lcomp O X N.subtype) (LinearMap.lcomp O X ι1) hinj
    have hcomp2 : LinearMap.lcomp O X ι1 ∘ₗ LinearMap.lcomp O X N.subtype = LinearMap.lcomp O X ι := by
      ext φ y
      rfl
    rw [hcomp2, h1, h2] at hc2
    rw [hc2, hc, mul_pow, mul_comm]

/- English proof (translation)
Introduce `O M X _ _ _ _ _ _ _ _ _ _ P hO hfin`. Establish `h` using `s5b7_main hO X (Nat.card (M ⧸ P)) P M P.subtype P.injective_subtype Nat.card_pos.ne' (by rw [Submodule.range_subtype])`. Conclude with `h`.
-/
theorem cardCokernelRestriction : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := by
  intro O M X _ _ _ _ _ _ _ _ _ _ P hO hfin
  have h := s5b7_main hO X (Nat.card (M ⧸ P)) P M P.subtype P.injective_subtype Nat.card_pos.ne'
    (by rw [Submodule.range_subtype])
  exact h

end homRestrict

section hermConj

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds

section herm

variable {F K : Type} [Field F] [CommRing K] [StarRing K] [Algebra F K]

/- English proof (translation)
Introduce `A hA`. Establish `hA' : Aᴴ = A` using `hA`. Express the relevant statement in the definitionally equal form `(g * (A * gᴴ))ᴴ = g * (A * gᴴ)`. Simplify using `[Matrix.conjTranspose_mul, hA', Matrix.mul_assoc]`.
-/
lemma s5b7_conj_mem {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) :
    ∀ A ∈ hermSub F K n hF, conjMap F g A ∈ hermSub F K n hF := by
  intro A hA
  have hA' : Aᴴ = A := hA
  change (g * (A * gᴴ))ᴴ = g * (A * gᴴ)
  simp [Matrix.conjTranspose_mul, hA', Matrix.mul_assoc]

noncomputable def congruenceRestrict {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) :
    hermSub F K n hF →ₗ[F] hermSub F K n hF :=
  (conjMap F g).restrict (s5b7_conj_mem hF g)

def s5b7_Q {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) : Prop :=
  algebraMap F K (LinearMap.det (congruenceRestrict hF g)) = (g.det * star g.det) ^ Fintype.card n

variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def borderedHermitian (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) :
    (hermSub F K n hF × (n → K) × F) →ₗ[F] Matrix (n ⊕ Unit) (n ⊕ Unit) K where
  toFun x := fromBlocks (x.1 : Matrix n n K) (replicateCol Unit x.2.1)
    (replicateRow Unit (star x.2.1)) (Matrix.of fun _ _ => algebraMap F K x.2.2)
  map_add' x y := by
    ext (i | i) (j | j) <;> simp
  map_smul' c x := by
    ext (i | i) (j | j)
    · simp
    · simp
    · simp [Algebra.smul_def, hF]
    · simp [Algebra.smul_def]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma borderedHermitian_apply (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (x : hermSub F K n hF × (n → K) × F) :
    borderedHermitian hF x = fromBlocks (x.1 : Matrix n n K) (replicateCol Unit x.2.1)
    (replicateRow Unit (star x.2.1)) (Matrix.of fun _ _ => algebraMap F K x.2.2) := rfl

/- English proof (translation)
Establish `h1 : (x.1 : Matrix n n K)ᴴ = x.1` using `x.1.2`. Express the relevant statement in the definitionally equal form `(borderedHermitian hF x)ᴴ = borderedHermitian hF x`. Rewrite using `[borderedHermitian_apply, fromBlocks_conjTranspose, h1]`. Rewrite using `[fromBlocks_inj]`. Use `⟨rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[conjTranspose_replicateRow]`. Simplify using `[conjTranspose_replicateCol]`. Use extensionality with `i j`. Simplify using `[hF]`.
-/
lemma borderedHermitian_mem (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (x : hermSub F K n hF × (n → K) × F) : borderedHermitian hF x ∈ hermSub F K (n ⊕ Unit) hF := by
  have h1 : (x.1 : Matrix n n K)ᴴ = x.1 := x.1.2
  change (borderedHermitian hF x)ᴴ = borderedHermitian hF x
  rw [borderedHermitian_apply, fromBlocks_conjTranspose, h1]
  rw [fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [conjTranspose_replicateRow]
  · simp [conjTranspose_replicateCol]
  · ext i j
    simp [hF]

noncomputable def s5b7_Psi (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (hfix : ∀ x : K, star x = x → x ∈ Set.range (algebraMap F K)) [Nontrivial K] :
    (hermSub F K n hF × (n → K) × F) ≃ₗ[F] hermSub F K (n ⊕ Unit) hF :=
  LinearEquiv.ofBijective ((borderedHermitian hF).codRestrict _ (borderedHermitian_mem hF)) (by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      change borderedHermitian hF x = borderedHermitian hF y at h
      rw [borderedHermitian_apply, borderedHermitian_apply, fromBlocks_inj] at h
      obtain ⟨h1, h2, -, h4⟩ := h
      have h2' : x.2.1 = y.2.1 := by
        funext i
        simpa using congrFun (congrFun h2 i) ()
      have h4' : x.2.2 = y.2.2 := by
        have := congrFun (congrFun h4 ()) ()
        exact (algebraMap F K).injective this
      exact Prod.ext (Subtype.ext h1) (Prod.ext h2' h4')
    · rintro ⟨X, hX⟩
      have hX' : Xᴴ = X := hX
      rw [← fromBlocks_toBlocks X, fromBlocks_conjTranspose, fromBlocks_inj] at hX'
      obtain ⟨h1, h2, h3, h4⟩ := hX'
      obtain ⟨f, hf⟩ := hfix (X.toBlocks₂₂ () ()) (by
        simpa using congrFun (congrFun h4 ()) ())
      refine ⟨(⟨X.toBlocks₁₁, h1⟩, fun i => X.toBlocks₁₂ i (), f), ?_⟩
      apply Subtype.ext
      change borderedHermitian hF _ = X
      rw [borderedHermitian_apply]
      conv_rhs => rw [← fromBlocks_toBlocks X]
      rw [fromBlocks_inj]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · ext i j
        rfl
      · rw [← h3]
        ext i j
        rfl
      · ext i j
        exact hf)

end herm

end hermConj

section volume

open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

/- English proof (translation)
Use `set v : Fin (r + 1) → V := Fin.cons v0 (fun b => c b • v0 + w b) with hv`. Use `set v' : Fin (r + 1) → V := Fin.cons v0 w with hv'`. Set `cc : Fin (r + 1) → ℂ` to `Fin.cons 0 c`. Establish `hvv : ∀ i, v i = cc i • v0 + v' i - (if i = 0 then 0 else 0)`. Introduce `i`.

Use `Fin.cases ?_ (fun b => ?_) i` and prove the remaining obligations. Simplify using `[hv, hv', cc]`. Simplify using `[hv, hv', cc]`. Establish `hvv' : ∀ i, v i = cc i • v' 0 + v' i`. Introduce `i`.

Rewrite using `[hvv i]`. Simplify using `[hv']`. Establish `h1 : (Matrix.gram ℂ v).det = (Matrix.of fun i j => inner ℂ (v' i) (v j)).det`. Use `Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => conj (cc i)) 0 (by simp [cc]) ?_` and prove the remaining obligations. Introduce `i j`.

Rewrite using `[Matrix.gram_apply, hvv' i, inner_add_left, inner_smul_left]`. Simplify using `only [Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (Matrix.of fun i j => inner ℂ (v' i) (v j)).det = (Matrix.gram ℂ v').det`. Rewrite using `[← Matrix.det_transpose, ← Matrix.det_transpose (Matrix.gram ℂ v')]`.

Use `Matrix.det_eq_of_forall_row_eq_smul_add_const cc 0 (by simp [cc]) ?_` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.transpose_apply, Matrix.transpose_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.gram_apply, Matrix.gram_apply, hvv' i, inner_add_right, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2, Matrix.det_succ_row_zero, Fin.sum_univ_succ]`.

Establish `h3 : ∀ j : Fin r, Matrix.gram ℂ v' 0 j.succ = 0`. Introduce `j`. Rewrite using `[Matrix.gram_apply]`. Simplify `hw j` using `[hv']`. Establish `h4 : (Matrix.gram ℂ v').submatrix Fin.succ (Fin.succAbove 0) = Matrix.gram ℂ w`.

Use extensionality with `i j`. Simplify using `[Matrix.gram_apply, hv']`. Establish `h5 : Matrix.gram ℂ v' 0 0 = (‖v0‖ : ℂ) ^ 2`. Rewrite using `[Matrix.gram_apply]`. Simplify using `[hv', inner_self_eq_norm_sq_to_K]`.

Rewrite using `[Finset.sum_eq_zero (fun j _ => by rw [h3 j]; ring), h4, h5]`. Simplify using the standard rewrite rules.
-/
lemma s5b7_gram_cons {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℕ) (v0 : V)
    (c : Fin r → ℂ) (w : Fin r → V) (hw : ∀ b, inner ℂ v0 (w b) = 0) :
    (Matrix.gram ℂ (Fin.cons v0 (fun b => c b • v0 + w b) : Fin (r + 1) → V)).det =
      ((‖v0‖ : ℂ) ^ 2) * (Matrix.gram ℂ w).det := by
  set v : Fin (r + 1) → V := Fin.cons v0 (fun b => c b • v0 + w b) with hv
  set v' : Fin (r + 1) → V := Fin.cons v0 w with hv'
  let cc : Fin (r + 1) → ℂ := Fin.cons 0 c
  have hvv : ∀ i, v i = cc i • v0 + v' i - (if i = 0 then 0 else 0) := by
    intro i
    refine Fin.cases ?_ (fun b => ?_) i
    · simp [hv, hv', cc]
    · simp [hv, hv', cc]
  have hvv' : ∀ i, v i = cc i • v' 0 + v' i := by
    intro i
    rw [hvv i]; simp [hv']
  have h1 : (Matrix.gram ℂ v).det = (Matrix.of fun i j => inner ℂ (v' i) (v j)).det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => conj (cc i)) 0 (by simp [cc]) ?_
    intro i j
    rw [Matrix.gram_apply, hvv' i, inner_add_left, inner_smul_left]
    simp only [Matrix.of_apply]
    ring
  have h2 : (Matrix.of fun i j => inner ℂ (v' i) (v j)).det = (Matrix.gram ℂ v').det := by
    rw [← Matrix.det_transpose, ← Matrix.det_transpose (Matrix.gram ℂ v')]
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const cc 0 (by simp [cc]) ?_
    intro i j
    rw [Matrix.transpose_apply, Matrix.transpose_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.gram_apply, Matrix.gram_apply, hvv' i, inner_add_right, inner_smul_right]
    ring
  rw [h1, h2, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h3 : ∀ j : Fin r, Matrix.gram ℂ v' 0 j.succ = 0 := by
    intro j
    rw [Matrix.gram_apply]
    simpa [hv'] using hw j
  have h4 : (Matrix.gram ℂ v').submatrix Fin.succ (Fin.succAbove 0) = Matrix.gram ℂ w := by
    ext i j
    simp [Matrix.gram_apply, hv']
  have h5 : Matrix.gram ℂ v' 0 0 = (‖v0‖ : ℂ) ^ 2 := by
    rw [Matrix.gram_apply]
    simp [hv', inner_self_eq_norm_sq_to_K]
  rw [Finset.sum_eq_zero (fun j _ => by rw [h3 j]; ring), h4, h5]
  simp

/- English proof (translation)
Establish `key : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (_ : finrank ℂ W = d + 1) (x : W) (_ : ‖x‖ = 1), ∃ b : OrthonormalBasis (Fin (d + 1)) ℂ W, b 0 = x`. Introduce `W _ _ _ hW x hx`. Establish `ho : Orthonormal ℂ (({0} : Set (Fin (d + 1))).domRestrict (fun _ => x))`. Rewrite using `[orthonormal_iff_ite]`. Introduce `i j`.

Establish `: i = j` using `Subsingleton.elim i j`. Substitute `this` using the available equality. Simplify using `[inner_self_eq_norm_sq_to_K, hx]`. Take `⟨b, hb⟩` from `ho.exists_orthonormalBasis_extension_of_card_eq (by simpa using hW)`. Conclude with `⟨b, hb 0 rfl⟩`.

Take `⟨b, hb⟩` from `key _ (by simp) u hu`. Take `⟨b', hb'⟩` from `key (WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) (by`. Rewrite using `[(WithLp.linearEquiv 2 ℂ (ℂ × EuclideanSpace ℂ (Fin d))).finrank_eq]`. Simplify using `[add_comm])`. Use the proof step `(WithLp.toLp 2 (1, 0)) (by simp)`.

Use `⟨b.repr.trans b'.repr.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, ← hb']`. Simplify using the standard rewrite rules.
-/
lemma s5b7_exists_iso (d : ℕ) (u : EuclideanSpace ℂ (Fin (d + 1))) (hu : ‖u‖ = 1) :
    ∃ Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)),
      Φ u = WithLp.toLp 2 (1, 0) := by
  have key : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (_ : finrank ℂ W = d + 1) (x : W) (_ : ‖x‖ = 1),
      ∃ b : OrthonormalBasis (Fin (d + 1)) ℂ W, b 0 = x := by
    intro W _ _ _ hW x hx
    have ho : Orthonormal ℂ (({0} : Set (Fin (d + 1))).domRestrict (fun _ => x)) := by
      rw [orthonormal_iff_ite]
      intro i j
      have : i = j := Subsingleton.elim i j
      subst this
      simp [inner_self_eq_norm_sq_to_K, hx]
    obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simpa using hW)
    exact ⟨b, hb 0 rfl⟩
  obtain ⟨b, hb⟩ := key _ (by simp) u hu
  obtain ⟨b', hb'⟩ := key (WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (by
      rw [(WithLp.linearEquiv 2 ℂ (ℂ × EuclideanSpace ℂ (Fin d))).finrank_eq]
      simp [add_comm])
    (WithLp.toLp 2 (1, 0)) (by simp)
  refine ⟨b.repr.trans b'.repr.symm, ?_⟩
  rw [← hb, ← hb']
  simp

/- English proof (translation)
Rewrite using `[(WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).finrank_eq, Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`.
-/
lemma s5b7_finrank_real (n : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).finrank_eq, Module.finrank_pi_fintype]
  simp [mul_comm]

/- English proof (translation)
Rewrite using `[Measure.real, InnerProductSpace.volume_ball, s5b7_finrank_real]`. Establish `h1 : Real.sqrt Real.pi ^ (2 * (d + 1)) = Real.pi ^ (d + 1)`. Rewrite using `[pow_mul, Real.sq_sqrt Real.pi_pos.le]`. Establish `h2 : Real.Gamma (((2 * (d + 1) : ℕ) : ℝ) / 2 + 1) = ((d + 1).factorial : ℝ)`. Rewrite using `[← Real.Gamma_nat_eq_factorial]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Simplify using `only [ENNReal.ofReal_one, one_pow, one_mul]`.

Conclude with `ENNReal.toReal_ofReal (by positivity)`.
-/
lemma s5b7_unit_ball (d : ℕ) :
    (volume : Measure (EuclideanSpace ℂ (Fin (d + 1)))).real (Metric.ball 0 1) =
      Real.pi ^ (d + 1) / ((d + 1).factorial : ℝ) := by
  rw [Measure.real, InnerProductSpace.volume_ball, s5b7_finrank_real]
  have h1 : Real.sqrt Real.pi ^ (2 * (d + 1)) = Real.pi ^ (d + 1) := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have h2 : Real.Gamma (((2 * (d + 1) : ℕ) : ℝ) / 2 + 1) = ((d + 1).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

/- English proof (translation)
Set `φ : ℝ → ℝ` to `fun ρ => if ρ ≤ R then (ρ ^ (2 * (d - r)))⁻¹ else 0`. Set `ψ : ℝ → ℝ` to `(Ioc 0 R).indicator (fun ρ => ρ ^ (2 * r + 1))`. Establish `hD` using `s5b7_finrank_real (d + 1)`. Establish `heq : EqOn (fun ρ : ℝ => ρ ^ (finrank ℝ (EuclideanSpace ℂ (Fin (d + 1))) - 1) • φ ρ) ψ (Ioi 0)`. Introduce `ρ hρ`.

Establish `hρ0 : (0 : ℝ) < ρ` using `hρ`. Simplify using `only [φ, ψ, hD, smul_eq_mul]`. Distinguish the cases in `h : ρ ≤ R`. Establish `hm : ρ ∈ Ioc 0 R` using `⟨hρ0, h⟩`. Rewrite using `[if_pos h, indicator_of_mem hm]`.

Establish `e : 2 * (d + 1) - 1 = 2 * (d - r) + (2 * r + 1)` using `by omega`. Rewrite using `[e, pow_add]`. Clear the denominators using the available nonvanishing facts. Establish `hm : ρ ∉ Ioc 0 R` using `fun hh => h hh.2`. Rewrite using `[if_neg h, indicator_of_notMem hm, mul_zero]`.

Establish `hψ : Integrable ψ`. Use `(IntegrableOn.integrable_indicator ?_ measurableSet_Ioc)` and prove the remaining obligations. Conclude with `(continuous_pow _).integrableOn_Ioc`. Establish `hint : Integrable (fun x : EuclideanSpace ℂ (Fin (d + 1)) => φ ‖x‖)`. Rewrite using `[integrable_fun_norm_addHaar volume]`.

Conclude with `(hψ.integrableOn).congr_fun heq.symm measurableSet_Ioi`. Establish `hval : ∫ x : EuclideanSpace ℂ (Fin (d + 1)), φ ‖x‖ = Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)`. Rewrite using `[integral_fun_norm_addHaar volume φ, setIntegral_congr_fun measurableSet_Ioi heq, s5b7_unit_ball, hD]`. Establish `h3 : ∫ ρ in Ioi (0 : ℝ), ψ ρ = R ^ (2 * r + 2) / (2 * (r : ℝ) + 2)`. Simplify using `only [ψ]`.

Rewrite using `[setIntegral_indicator measurableSet_Ioc]`. Establish `: Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R`. Use extensionality with `x`. Simplify using `only [mem_inter_iff, mem_Ioi, mem_Ioc]`. The claim follows by propositional logic.

Rewrite using `[this, ← intervalIntegral.integral_of_le hR.le, integral_pow]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, Nat.factorial_succ]`. Simplify using `only [nsmul_eq_mul, smul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← hval]`. Use `(ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => ?_)).symm` and prove the remaining obligations. Simplify using `only [φ, Pi.zero_apply]`.

Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
lemma s5b7_radial (d r : ℕ) (hr : r ≤ d) (R : ℝ) (hR : 0 < R) :
    ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
      ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * (d - r)))⁻¹ else 0) =
    ENNReal.ofReal (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by
  let φ : ℝ → ℝ := fun ρ => if ρ ≤ R then (ρ ^ (2 * (d - r)))⁻¹ else 0
  let ψ : ℝ → ℝ := (Ioc 0 R).indicator (fun ρ => ρ ^ (2 * r + 1))
  have hD := s5b7_finrank_real (d + 1)
  have heq : EqOn (fun ρ : ℝ => ρ ^ (finrank ℝ (EuclideanSpace ℂ (Fin (d + 1))) - 1) • φ ρ) ψ
      (Ioi 0) := by
    intro ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    simp only [φ, ψ, hD, smul_eq_mul]
    by_cases h : ρ ≤ R
    · have hm : ρ ∈ Ioc 0 R := ⟨hρ0, h⟩
      rw [if_pos h, indicator_of_mem hm]
      have e : 2 * (d + 1) - 1 = 2 * (d - r) + (2 * r + 1) := by omega
      rw [e, pow_add]
      field_simp
    · have hm : ρ ∉ Ioc 0 R := fun hh => h hh.2
      rw [if_neg h, indicator_of_notMem hm, mul_zero]
  have hψ : Integrable ψ := by
    refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioc)
    exact (continuous_pow _).integrableOn_Ioc
  have hint : Integrable (fun x : EuclideanSpace ℂ (Fin (d + 1)) => φ ‖x‖) := by
    rw [integrable_fun_norm_addHaar volume]
    exact (hψ.integrableOn).congr_fun heq.symm measurableSet_Ioi
  have hval : ∫ x : EuclideanSpace ℂ (Fin (d + 1)), φ ‖x‖ =
      Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1) := by
    rw [integral_fun_norm_addHaar volume φ, setIntegral_congr_fun measurableSet_Ioi heq,
      s5b7_unit_ball, hD]
    have h3 : ∫ ρ in Ioi (0 : ℝ), ψ ρ = R ^ (2 * r + 2) / (2 * (r : ℝ) + 2) := by
      simp only [ψ]
      rw [setIntegral_indicator measurableSet_Ioc]
      have : Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto
      rw [this, ← intervalIntegral.integral_of_le hR.le, integral_pow]
      simp
      ring
    rw [h3, Nat.factorial_succ]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
  rw [← hval]
  refine (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => ?_)).symm
  simp only [φ, Pi.zero_apply]
  split_ifs
  · positivity
  · exact le_rfl

def s5b7_A (R : ℝ) (d r : ℕ) (t : ℝ) : Set (Fin r → EuclideanSpace ℂ (Fin d)) :=
  {a | (∀ b, ‖a b‖ ≤ R) ∧ Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ t}

/- English proof (translation)
Establish `h1 : IsClosed {a : Fin r → EuclideanSpace ℂ (Fin d) | ∀ b, ‖a b‖ ≤ R}`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun b => isClosed_le (by fun_prop) continuous_const`. Establish `h2 : Continuous fun a : Fin r → EuclideanSpace ℂ (Fin d) => Real.sqrt ‖(Matrix.gram ℂ a).det‖`. Use `Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))` and prove the remaining obligations.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.gram_apply]`. Conclude with `(continuous_apply i).inner (continuous_apply j)`. Conclude with `h1.inter (isClosed_le h2 continuous_const)`.
-/
lemma s5b7_A_closed (R : ℝ) (d r : ℕ) (t : ℝ) : IsClosed (s5b7_A R d r t) := by
  have h1 : IsClosed {a : Fin r → EuclideanSpace ℂ (Fin d) | ∀ b, ‖a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_le (by fun_prop) continuous_const
  have h2 : Continuous fun a : Fin r → EuclideanSpace ℂ (Fin d) =>
      Real.sqrt ‖(Matrix.gram ℂ a).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply i).inner (continuous_apply j)
  exact h1.inter (isClosed_le h2 continuous_const)

/- English proof (translation)
Establish `h1` using `volume_preserving_pi (fun _ : Fin r => hf)`. Establish `h2` using `volume_preserving_pi (fun _ : Fin r => hg)`. Establish `h3` using `volume_measurePreserving_arrowProdEquivProdArrow γ δ (Fin r)`. Conclude with `h3.comp (h2.comp h1)`.
-/
lemma measurePreserving_pi_comp_prod {α β γ δ : Type*} [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ]
    [MeasureSpace δ] [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    [SigmaFinite (volume : Measure γ)] [SigmaFinite (volume : Measure δ)] (r : ℕ) (f : α → β)
    (g : β → γ × δ) (hf : MeasurePreserving f) (hg : MeasurePreserving g) :
    MeasurePreserving (fun a : Fin r → α =>
      ((fun b => (g (f (a b))).1), (fun b => (g (f (a b))).2))) volume volume := by
  have h1 := volume_preserving_pi (fun _ : Fin r => hf)
  have h2 := volume_preserving_pi (fun _ : Fin r => hg)
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow γ δ (Fin r)
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Establish `h0 : MeasurePreserving (Φ : EuclideanSpace ℂ (Fin (d + 1)) → WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))` using `LinearIsometryEquiv.measurePreserving ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))`. Conclude with `measurePreserving_pi_comp_prod r _ _ h0 (WithLp.volume_preserving_ofLp ℂ (EuclideanSpace ℂ (Fin d)))`.
-/
lemma s5b7_mp (d r : ℕ)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :
    MeasurePreserving (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
      ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) volume volume := by
  have h0 : MeasurePreserving
      (Φ : EuclideanSpace ℂ (Fin (d + 1)) → WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :=
    LinearIsometryEquiv.measurePreserving
      ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } :
        EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
  exact measurePreserving_pi_comp_prod r _ _ h0 (WithLp.volume_preserving_ofLp ℂ (EuclideanSpace ℂ (Fin d)))

/- English proof (translation)
Take `⟨hn, hg⟩` from `h`. Establish `hx0 : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Establish `hxc : ((‖x‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hx0.ne'`. Establish `hnb : ∀ b, ‖a' b‖ ≤ R` using `fun b => by simpa using hn b.succ`. Establish `hsq : ∀ b, ‖(Φ (a' b)).ofLp.1‖ ^ 2 + ‖(Φ (a' b)).ofLp.2‖ ^ 2 = ‖a' b‖ ^ 2`.

Introduce `b`. Rewrite using `[← Φ.norm_map (a' b), WithLp.prod_norm_sq_eq_of_L2]`. Both sides reduce to the same expression. Establish `hR0 : ∀ b, 0 ≤ ‖a' b‖` using `fun b => norm_nonneg _`. Establish `hΦx : Φ x = ((‖x‖ : ℝ) : ℂ) • WithLp.toLp 2 ((1 : ℂ), (0 : EuclideanSpace ℂ (Fin d)))`.

Rewrite using `[← hΦ, map_smul, smul_smul]`. Use `push_cast`. Rewrite using `[mul_inv_cancel₀ hxc, one_smul]`. Use `⟨fun b => ?_, fun b => ?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ (hnb b)` and prove the remaining obligations.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.2‖])`. Use `le_trans ?_ (hnb b)` and prove the remaining obligations. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.1‖])`. Establish `hgram : (Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1)))).det = (((‖x‖ : ℝ) : ℂ) ^ 2) * (Matrix.gram ℂ (fun b => (Φ (a' b)).ofLp.2)).det`. Establish `e1 : Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) = Matrix.gram ℂ (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → _) i))`.

Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply, Φ.inner_map_map]`. Establish `e2 : (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) i)) = Fin.cons (Φ x) (fun b => ((Φ (a' b)).ofLp.1 / ((‖x‖ : ℝ) : ℂ)) • Φ x + WithLp.toLp 2 ((0 : ℂ), (Φ (a' b)).ofLp.2))`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun b => ?_) i` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `only [Fin.cons_succ]`. Rewrite using `[hΦx, smul_smul, div_mul_cancel₀ _ hxc]`. Apply `WithLp.ofLp_injective 2` to reduce the goal to its premises. Apply the tactic sequence `apply Prod.ext <;> simp`.

Rewrite using `[e1, e2, s5b7_gram_cons]`. Rewrite using `[Φ.norm_map]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[Matrix.gram_apply, WithLp.prod_inner_apply]`.

Introduce `b`. Rewrite using `[hΦx]`. Simplify using `[WithLp.prod_inner_apply]`. Rewrite `hg` using `[hgram, norm_mul, norm_pow, Complex.norm_real, norm_norm, Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]`. Rewrite using `[le_div_iff₀ hx0]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma s5b7_slice (R : ℝ) (d r : ℕ) (t : ℝ) (x : EuclideanSpace ℂ (Fin (d + 1))) (hx : x ≠ 0)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (hΦ : Φ (((‖x‖⁻¹ : ℝ) : ℂ) • x) = WithLp.toLp 2 (1, 0))
    (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1)))
    (h : (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈ s5b7_A R (d + 1) (r + 1) t) :
    (∀ b, ‖(Φ (a' b)).ofLp.1‖ ≤ R) ∧ (fun b => (Φ (a' b)).ofLp.2) ∈ s5b7_A R d r (t / ‖x‖) := by
  obtain ⟨hn, hg⟩ := h
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxc : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hnb : ∀ b, ‖a' b‖ ≤ R := fun b => by simpa using hn b.succ
  have hsq : ∀ b, ‖(Φ (a' b)).ofLp.1‖ ^ 2 + ‖(Φ (a' b)).ofLp.2‖ ^ 2 = ‖a' b‖ ^ 2 := by
    intro b
    rw [← Φ.norm_map (a' b), WithLp.prod_norm_sq_eq_of_L2]
    rfl
  have hR0 : ∀ b, 0 ≤ ‖a' b‖ := fun b => norm_nonneg _
  have hΦx : Φ x = ((‖x‖ : ℝ) : ℂ) • WithLp.toLp 2 ((1 : ℂ), (0 : EuclideanSpace ℂ (Fin d))) := by
    rw [← hΦ, map_smul, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hxc, one_smul]
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  · refine le_trans ?_ (hnb b)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.2‖])
  · refine le_trans ?_ (hnb b)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.1‖])
  · have hgram : (Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1)))).det =
        (((‖x‖ : ℝ) : ℂ) ^ 2) * (Matrix.gram ℂ (fun b => (Φ (a' b)).ofLp.2)).det := by
      have e1 : Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) =
          Matrix.gram ℂ (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → _) i)) := by
        ext i j
        simp only [Matrix.gram_apply, Φ.inner_map_map]
      have e2 : (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) i)) =
          Fin.cons (Φ x) (fun b => ((Φ (a' b)).ofLp.1 / ((‖x‖ : ℝ) : ℂ)) • Φ x +
            WithLp.toLp 2 ((0 : ℂ), (Φ (a' b)).ofLp.2)) := by
        funext i
        refine Fin.cases ?_ (fun b => ?_) i
        · simp
        · simp only [Fin.cons_succ]
          rw [hΦx, smul_smul, div_mul_cancel₀ _ hxc]
          apply WithLp.ofLp_injective 2
          apply Prod.ext <;> simp
      rw [e1, e2, s5b7_gram_cons]
      · rw [Φ.norm_map]
        congr 2
        ext i j
        simp [Matrix.gram_apply, WithLp.prod_inner_apply]
      · intro b
        rw [hΦx]
        simp [WithLp.prod_inner_apply]
    rw [hgram, norm_mul, norm_pow, Complex.norm_real, norm_norm, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx0.le] at hg
    rw [le_div_iff₀ hx0]
    linarith

/- English proof (translation)
Establish `hs0 : (0 : ℝ) < (s.factorial : ℝ)` using `by exact_mod_cast s.factorial_pos`. Establish `hd0 : (0 : ℝ) < (d.factorial : ℝ)` using `by exact_mod_cast d.factorial_pos`. Establish `hsd : (s.factorial : ℝ) ≤ (d.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_le hs`. Establish `hpi` using `Real.pi_pos`. Establish `e1 : (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) / (s.factorial : ℝ) ^ r) * (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) = t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) / ((s.factorial : ℝ) ^ r * (( …`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, pow_succ (s.factorial : ℝ) r]`. Establish `h1 : (s.factorial : ℝ) ≤ (d.factorial : ℝ) * ((r : ℝ) + 1)`. Establish `: (0 : ℝ) ≤ (r : ℝ)` using `Nat.cast_nonneg r`.

Use the polynomial consequences of the given equalities and inequalities. Use `gcongr`.
-/
lemma s5b7_real_ineq (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) (r d s : ℕ) (hs : s ≤ d) :
    (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) *
      (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) ≤
    t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
      (s.factorial : ℝ) ^ (r + 1) := by
  have hs0 : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast s.factorial_pos
  have hd0 : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast d.factorial_pos
  have hsd : (s.factorial : ℝ) ≤ (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hs
  have hpi := Real.pi_pos
  have e1 : (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) *
      (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) =
      t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
        ((s.factorial : ℝ) ^ r * ((d.factorial : ℝ) * ((r : ℝ) + 1))) := by
    field_simp
    ring
  rw [e1, pow_succ (s.factorial : ℝ) r]
  have h1 : (s.factorial : ℝ) ≤ (d.factorial : ℝ) * ((r : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith
  gcongr

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `d _ t ht`. Distinguish the cases in `h1 : 1 ≤ t`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_one]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Simplify using `only [pow_zero, mul_one, zero_mul, div_one, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]`. Conclude with `one_le_pow₀ h1`.

Establish `: s5b7_A R d 0 t = ∅`. Use extensionality with `a`. Simplify using `only [s5b7_A, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]`. Introduce `_`. Simplify using `using h1`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `d hd t ht`. Take `⟨d, rfl⟩ : ∃ d', d = d' + 1` from `⟨d - 1, by omega⟩`.

Establish `hr : r ≤ d` using `by omega`. Establish `hs' : d + 1 - (r + 1) = d - r` using `by omega`. Rewrite using `[hs']`. Use `set s := d - r with hs`. Set `e` to `MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0`.

Establish `he : MeasurePreserving e` using `volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0`. Establish `hAm : MeasurableSet (s5b7_A R (d + 1) (r + 1) t)` using `(s5b7_A_closed _ _ _ _).measurableSet`. Establish `hes : ∀ (x : EuclideanSpace ℂ (Fin (d + 1))) (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1))), e.symm (x, a') = Fin.cons x a'`. Introduce `x a'`. Simplify using `only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]`.

Conclude with `Fin.insertNth_zero' x a'`. Establish `hvol : volume (s5b7_A R (d + 1) (r + 1) t) = ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))`. Rewrite using `[← (he.symm e).measure_preimage hAm.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply (e.symm.measurable hAm)]`. Rewrite using `[hvol]`. Use `set C1 : ℝ := (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) / (s.factorial : ℝ) ^ r) with hC1def`.

Establish `hC1 : 0 ≤ C1` using `by positivity`. Establish `hbound : ∀ᵐ x : EuclideanSpace ℂ (Fin (d + 1)), volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) ≤ ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0)`. Establish `h0 : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin (d + 1)))) ∈ ae volume` using `compl_mem_ae_iff.mpr (measure_singleton 0)`. Use `filter_upwards [h0] with x hx`. Establish `hx : x ≠ 0` using `hx`.

Distinguish the cases in `hxR : ‖x‖ ≤ R`. Rewrite using `[if_pos hxR]`. Establish `hx0 : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Take `⟨Φ, hΦ⟩` from `s5b7_exists_iso d (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by`. Rewrite using `[norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne'])`.

Use `set S : Set ((Fin r → ℂ) × (Fin r → EuclideanSpace ℂ (Fin d))) := (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) R) ×ˢ s5b7_A R d r (t / ‖x‖) with hS`. Establish `hsub : Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) ⊆ (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) => ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) ⁻¹' S`. Introduce `a' ha'`. Establish `ha'' : (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈ s5b7_A R (d + 1) (r + 1) t`. Rewrite using `[← hes]`.

Conclude with `ha'`. Take `⟨h1, h2⟩` from `s5b7_slice R d r t x hx Φ hΦ a' ha''`. Conclude with `⟨fun b _ => by simpa using h1 b, h2⟩`. Establish `hSm : MeasurableSet S` using `(MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet).prod (s5b7_A_closed _ _ _ _).measurableSet`. Establish `hball : volume (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) = ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r)`.

Rewrite using `[volume_pi_pi]`. Simplify using `only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hR.le]`. Use `congr 2`. Conclude with `(ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hS, Measure.volume_eq_prod, Measure.prod_prod]`. Use `_ ≤ ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) * ENNReal.ofReal ((t / ‖x‖) ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) / (s.factorial : ℝ) ^ r) := by`. Rewrite using `[hball]`. Use `gcongr`.

Conclude with `ih d hr _ (by positivity)`. Use `_ = ENNReal.ofReal C1 * ENNReal.ofReal ((‖x‖ ^ (2 * s))⁻¹) := by`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC1]`. Use `congr 1`. Rewrite using `[hC1def, div_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `: Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) = ∅`. Use extensionality with `a'`. Simplify using `only [mem_preimage, mem_empty_iff_false, iff_false]`. Rewrite using `[hes]`.

Introduce `h`. Conclude with `hxR (by simpa using h.1 0)`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hs, s5b7_radial d r hr R hR]`. Use `_ = ENNReal.ofReal (C1 * (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1))) := (ENNReal.ofReal_mul hC1).symm`. Use `_ ≤ _ := ENNReal.ofReal_le_ofReal (s5b7_real_ineq R t hR ht r d s (Nat.sub_le d r))`.
-/
theorem s5b7_vol (R : ℝ) (hR : 0 < R) : ∀ (r d : ℕ), r ≤ d → ∀ t : ℝ, 0 ≤ t →
    volume (s5b7_A R d r t) ≤ ENNReal.ofReal (t ^ (2 * (d - r)) * R ^ (2 * r ^ 2) *
      Real.pi ^ (r * d) / ((d - r).factorial : ℝ) ^ r) := by
  intro r
  induction r with
  | zero =>
    intro d _ t ht
    by_cases h1 : 1 ≤ t
    · calc volume (s5b7_A R d 0 t) ≤ volume (univ : Set (Fin 0 → EuclideanSpace ℂ (Fin d))) :=
            measure_mono (subset_univ _)
        _ = 1 := by rw [Measure.volume_pi_eq_dirac 0]; simp
        _ ≤ _ := by
            rw [← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            simp only [pow_zero, mul_one, zero_mul, div_one, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow]
            exact one_le_pow₀ h1
    · have : s5b7_A R d 0 t = ∅ := by
        ext a
        simp only [s5b7_A, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _
        simpa using h1
      rw [this]; simp
  | succ r ih =>
    intro d hd t ht
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hr : r ≤ d := by omega
    have hs' : d + 1 - (r + 1) = d - r := by omega
    rw [hs']
    set s := d - r with hs
    let e := MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove
      (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0
    have hAm : MeasurableSet (s5b7_A R (d + 1) (r + 1) t) := (s5b7_A_closed _ _ _ _).measurableSet
    have hes : ∀ (x : EuclideanSpace ℂ (Fin (d + 1))) (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1))),
        e.symm (x, a') = Fin.cons x a' := by
      intro x a'
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' x a'
    have hvol : volume (s5b7_A R (d + 1) (r + 1) t) =
        ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) := by
      rw [← (he.symm e).measure_preimage hAm.nullMeasurableSet, Measure.volume_eq_prod,
        Measure.prod_apply (e.symm.measurable hAm)]
    rw [hvol]
    set C1 : ℝ := (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) with hC1def
    have hC1 : 0 ≤ C1 := by positivity
    have hbound : ∀ᵐ x : EuclideanSpace ℂ (Fin (d + 1)),
        volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) ≤
          ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) := by
      have h0 : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin (d + 1)))) ∈ ae volume :=
        compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [h0] with x hx
      have hx : x ≠ 0 := hx
      by_cases hxR : ‖x‖ ≤ R
      · rw [if_pos hxR]
        have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
        obtain ⟨Φ, hΦ⟩ := s5b7_exists_iso d (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
          rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne'])
        set S : Set ((Fin r → ℂ) × (Fin r → EuclideanSpace ℂ (Fin d))) :=
          (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) R) ×ˢ s5b7_A R d r (t / ‖x‖) with hS
        have hsub : Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) ⊆
            (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
              ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) ⁻¹' S := by
          intro a' ha'
          have ha'' : (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈
              s5b7_A R (d + 1) (r + 1) t := by
            rw [← hes]; exact ha'
          obtain ⟨h1, h2⟩ := s5b7_slice R d r t x hx Φ hΦ a' ha''
          exact ⟨fun b _ => by simpa using h1 b, h2⟩
        have hSm : MeasurableSet S :=
          (MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet).prod
            (s5b7_A_closed _ _ _ _).measurableSet
        have hball : volume (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) =
            ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) := by
          rw [volume_pi_pi]
          simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow hR.le]
          congr 2
          exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
        calc volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
            ≤ volume ((fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
              ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) ⁻¹' S) :=
              measure_mono hsub
          _ = volume S := (s5b7_mp d r Φ).measure_preimage hSm.nullMeasurableSet
          _ = volume (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) *
                volume (s5b7_A R d r (t / ‖x‖)) := by
              rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
          _ ≤ ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) *
                ENNReal.ofReal ((t / ‖x‖) ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
                  (s.factorial : ℝ) ^ r) := by
              rw [hball]
              gcongr
              exact ih d hr _ (by positivity)
          _ = ENNReal.ofReal C1 * ENNReal.ofReal ((‖x‖ ^ (2 * s))⁻¹) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC1]
              congr 1
              rw [hC1def, div_pow]
              field_simp
      · have : Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) = ∅ := by
          ext a'
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          rw [hes]
          intro h
          exact hxR (by simpa using h.1 0)
        rw [this]; simp
    calc ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
        ≤ ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
            ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) :=
          lintegral_mono_ae hbound
      _ = ENNReal.ofReal C1 * ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
            ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C1 * ENNReal.ofReal
            (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by
          rw [hs, s5b7_radial d r hr R hR]
      _ = ENNReal.ofReal (C1 *
            (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1))) :=
          (ENNReal.ofReal_mul hC1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (s5b7_real_ineq R t hR ht r d s (Nat.sub_le d r))

end volume

end Formalism.HermitianLatticeCounting.P
