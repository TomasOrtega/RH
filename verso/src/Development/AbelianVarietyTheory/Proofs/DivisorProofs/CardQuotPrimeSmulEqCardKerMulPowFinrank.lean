import Mathlib
open CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `f.range.card_mul_index`. Establish `h2` using `f.ker.card_mul_index`. Rewrite `h2` using `[AddSubgroup.index_ker]`. Establish `h3 : 0 < Nat.card f.range` using `Nat.card_pos`. Apply `Nat.eq_of_mul_eq_mul_left h3` to reduce the goal to its premises.

Rewrite using `[h1, mul_comm, h2]`.
-/
theorem index_range_eq_card_ker_of_finite {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have h3 : 0 < Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left h3
  rw [h1, mul_comm, h2]

/- English proof (translation)
Establish `hp' : (p : ℤ) ≠ 0` using `by exact_mod_cast hp`. Set `f : D →+ D` to `zsmulAddGroupHom (p : ℤ)`. Establish `hf : ∀ d, f d = (p : ℤ) • d` using `fun d => rfl`. Establish `hrank : Module.finrank ℤ M = n`. Rewrite using `[e.toIntLinearEquiv.finrank_eq]`.

Establish `hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0`. Rewrite using `[Module.rank_eq_zero_iff_isTorsion]`. Introduce `x`. Use `⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(Nat.card_pos (α := D)).ne'` after adjusting the coercions.

Establish `hx : x.1.1 = 0` using `x.2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Submonoid.smul_def, hx]`. Simplify using `[Submonoid.smul_def]`.

Establish `: Module.rank ℤ ((Fin n → ℤ) × D) = n`. Rewrite using `[← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD, LinearMap.range_eq_top.2 LinearMap.fst_surjective]`. Simplify using the standard rewrite rules. Simplify using `[Module.finrank, this]`. Establish `hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card f.ker`.

Use `Nat.card_congr { toFun := fun x => ⟨(e x.1).2, ?_⟩ invFun := fun d => ⟨e.symm (0, d.1), ?_⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations. Establish `hx : (p : ℤ) • x.1 = 0` using `x.2`. Use `congrArg (fun y => (e y).2) hx` as an intermediate fact. Simplify `this` using `[hf]`. Establish `hd : (p : ℤ) • d.1 = 0` using `d.2`.

Express the relevant statement in the definitionally equal form `(p : ℤ) • e.symm (0, d.1) = 0`. Rewrite using `[← map_zsmul, Prod.smul_mk, hd, smul_zero]`. Conclude with `map_zero _`. Introduce `x`. Establish `hx : (p : ℤ) • x.1 = 0` using `x.2`.

Establish `h1 : (p : ℤ) • (e x.1).1 = 0`. Use `congrArg (fun y => (e y).1) hx` as an intermediate fact. Simplify `this` using `only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero]`. Establish `h2 : (e x.1).1 = 0` using `(smul_eq_zero.1 h1).resolve_left hp'`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `e.symm (0, (e x.1).2) = x.1`. Rewrite using `[← h2]`. Conclude with `e.symm_apply_apply _`. Introduce `d`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Establish `hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup = ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod f.range).comap e.toAddMonoidHom`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Rewrite using `[AddSubgroup.mem_comap]`. Express the relevant statement in the definitionally equal form `e ((p : ℤ) • y) ∈ _`. Rewrite using `[map_zsmul]`. Use `⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩` and prove the remaining obligations. Simplify using `[mul_comm]`.

Introduce and unpack `⟨h1, d, hd⟩`. Establish `h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i` using `fun i => h1 i (Set.mem_univ i)`. Use `choose k hk using h1'`. Use `⟨e.symm (k, d), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(p : ℤ) • e.symm (k, d) = x`.

Rewrite using `[← map_zsmul, AddEquiv.symm_apply_eq]`. Use `Prod.ext (funext fun i => ?_) hd` and prove the remaining obligations. Rewrite using `[← hk i]`. Simplify using `[mul_comm]`. Establish `hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index` using `rfl`.

Rewrite using `[hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod, AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]`. Simplify using `[Int.index_zmultiples]`.
-/
theorem card_quot_smul_eq_of_equiv_prod {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  let f : D →+ D := zsmulAddGroupHom (p : ℤ)
  have hf : ∀ d, f d = (p : ℤ) • d := fun d => rfl
  have hrank : Module.finrank ℤ M = n := by
    rw [e.toIntLinearEquiv.finrank_eq]
    have hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0 := by
      rw [Module.rank_eq_zero_iff_isTorsion]
      intro x
      refine ⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      · exact_mod_cast (Nat.card_pos (α := D)).ne'
      · have hx : x.1.1 = 0 := x.2
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp [Submonoid.smul_def, hx]
        · simp [Submonoid.smul_def]
    have : Module.rank ℤ ((Fin n → ℤ) × D) = n := by
      rw [← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD,
        LinearMap.range_eq_top.2 LinearMap.fst_surjective]
      simp
    simp [Module.finrank, this]
  have hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(e x.1).2, ?_⟩
        invFun := fun d => ⟨e.symm (0, d.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (p : ℤ) • x.1 = 0 := x.2
      have := congrArg (fun y => (e y).2) hx
      simpa [hf] using this
    · have hd : (p : ℤ) • d.1 = 0 := d.2
      change (p : ℤ) • e.symm (0, d.1) = 0
      rw [← map_zsmul, Prod.smul_mk, hd, smul_zero]
      exact map_zero _
    · intro x
      have hx : (p : ℤ) • x.1 = 0 := x.2
      have h1 : (p : ℤ) • (e x.1).1 = 0 := by
        have := congrArg (fun y => (e y).1) hx
        simpa only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero] using this
      have h2 : (e x.1).1 = 0 := (smul_eq_zero.1 h1).resolve_left hp'
      apply Subtype.ext
      change e.symm (0, (e x.1).2) = x.1
      rw [← h2]
      exact e.symm_apply_apply _
    · intro d
      apply Subtype.ext
      simp
  have hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup =
      ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod
        f.range).comap e.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [AddSubgroup.mem_comap]
      change e ((p : ℤ) • y) ∈ _
      rw [map_zsmul]
      refine ⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩
      simp [mul_comm]
    · rintro ⟨h1, d, hd⟩
      have h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i := fun i => h1 i (Set.mem_univ i)
      choose k hk using h1'
      refine ⟨e.symm (k, d), ?_⟩
      change (p : ℤ) • e.symm (k, d) = x
      rw [← map_zsmul, AddEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => ?_) hd
      rw [← hk i]
      simp [mul_comm]
  have hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index := rfl
  rw [hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod,
    AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]
  simp [Int.index_zmultiples]

/- English proof (translation)
Take `rfl : inst = AddCommGroup.toIntModule M` from `Subsingleton.elim _ _`. Use `haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance`. Take `⟨n, ι, _, q, hq, k, ⟨e⟩⟩` from `AddCommGroup.equiv_free_prod_directSum_zmod M`. Use `haveI : ∀ i, NeZero (q i ^ k i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩`. Use `haveI : Finite (DirectSum ι fun i => ZMod (q i ^ k i)) := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm`.

Conclude with `card_quot_smul_eq_of_equiv_prod (e.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl _))) p (Fact.out : p.Prime).ne_zero`.
-/
theorem card_quot_prime_smul_eq_card_ker_mul_pow_finrank (M : Type) [AddCommGroup M]
    [inst : Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨n, ι, _, q, hq, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ k i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ k i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact card_quot_smul_eq_of_equiv_prod
    (e.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl _)))
    p (Fact.out : p.Prime).ne_zero

end GlobalTheory
