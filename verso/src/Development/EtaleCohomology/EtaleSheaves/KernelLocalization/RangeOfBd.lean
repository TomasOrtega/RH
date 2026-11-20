import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex CochainComplex.HomComplex LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

variable (R : Type) [CommRing R] (F : Shv R)

def bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) : H R U F m →+ Hrel R f F n :=
  HK.pre R (mappingCone.fst ((chains R).map f)) F m n h

/- English proof (translation)
Take `⟨w, rfl⟩` from `w.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp _ (zcomp (Cocycle.ofHom ((chains R).map f)) w (zero_add m)) h) = 0`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`. Use `⟨m, by omega, n.negOnePow • (mappingCone.snd ((chains R).map f)).comp w.1 (zero_add m), ?_⟩` and prove the remaining obligations. Rewrite using `[δ_units_smul, δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd]`.

Express the relevant statement in the definitionally equal form `_ = (mappingCone.fst ((chains R).map f)).1.comp ((Cochain.ofHom ((chains R).map f)).comp w.1 (zero_add m)) h`. Establish `hn : n.negOnePow = - m.negOnePow` using `by rw [← h, add_comm, Int.negOnePow_succ]`. Simplify using `[hn, smul_smul]`.
-/
theorem bd_pull {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (w : H R E F m) :
    bd R F f m n h (pull R f F m w) = 0 := by
  obtain ⟨w, rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp _ (zcomp (Cocycle.ofHom ((chains R).map f)) w (zero_add m)) h) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, by omega, n.negOnePow • (mappingCone.snd ((chains R).map f)).comp w.1 (zero_add m), ?_⟩
  rw [δ_units_smul, δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd]
  change _ = (mappingCone.fst ((chains R).map f)).1.comp ((Cochain.ofHom ((chains R).map f)).comp w.1 (zero_add m)) h
  have hn : n.negOnePow = - m.negOnePow := by rw [← h, add_comm, Int.negOnePow_succ]
  simp [hn, smul_smul]

/- English proof (translation)
Take `⟨c, rfl⟩` from `z.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hz`. Rewrite `hz` using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)]`. Take `⟨γ, hγ⟩` from `hz`. Express the relevant statement in the definitionally equal form `δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ`.

Set `a : Cochain ((chains R).obj U) (res R F) m` to `(mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by omega) + m.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)`. Establish `key : (mappingCone.fst ((chains R).map f)).1.comp a h = c.1 - δ m n ((mappingCone.snd ((chains R).map f)).comp γ (zero_add m))`. Rewrite using `[δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd, hγ, mappingCone.ext_cochain_from_iff _ m n (by omega)]`. Prove the components needed by the constructor for the conclusion. Simplify using `[a]`.

Simplify using `[a]`. Establish `ha : δ m n a = 0`. Establish `h1` using `congrArg (δ n (n + 1)) key`. Rewrite `h1` using `[δ_sub, δ_δ, Cocycle.δ_eq_zero, δ_comp _ _ _ 2 n (n + 1) (by omega) (by omega) (by omega), Cocycle.δ_eq_zero]`. Establish `h2` using `congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by omega)) h1`.

Simplify using `using h2`. Use `⟨CohomologyClass.mk (Cocycle.mk a n (by omega) ha), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp _ _ h) = _`. Rewrite using `[eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]`. Use `⟨m, by omega, (mappingCone.snd ((chains R).map f)).comp γ (zero_add m), ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = c.1 - (mappingCone.fst ((chains R).map f)).1.comp a h`. Rewrite using `[key]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (z : Hrel R f F n) (hz : fgt R f F n z = 0) :
    ∃ y, bd R F f m n h y = z := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hz
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)] at hz
  obtain ⟨γ, hγ⟩ := hz
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  let a : Cochain ((chains R).obj U) (res R F) m :=
    (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by omega) +
      m.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)
  have key : (mappingCone.fst ((chains R).map f)).1.comp a h =
      c.1 - δ m n ((mappingCone.snd ((chains R).map f)).comp γ (zero_add m)) := by
    rw [δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd, hγ,
      mappingCone.ext_cochain_from_iff _ m n (by omega)]
    constructor
    · simp [a]
    · simp [a]
  have ha : δ m n a = 0 := by
    have h1 := congrArg (δ n (n + 1)) key
    rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, δ_comp _ _ _ 2 n (n + 1) (by omega) (by omega) (by omega),
      Cocycle.δ_eq_zero] at h1
    have h2 := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by omega)) h1
    simpa using h2
  refine ⟨CohomologyClass.mk (Cocycle.mk a n (by omega) ha), ?_⟩
  change CohomologyClass.mk (zcomp _ _ h) = _
  rw [eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, by omega, (mappingCone.snd ((chains R).map f)).comp γ (zero_add m), ?_⟩
  change _ = c.1 - (mappingCone.fst ((chains R).map f)).1.comp a h
  rw [key]; abel

/- English proof (translation)
Take `⟨y, rfl⟩` from `y.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp _ y h) = 0 at hy`. Rewrite `hy` using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)]`. Take `⟨β, hβ⟩` from `hy`. Express the relevant statement in the definitionally equal form `δ m n β = (mappingCone.fst ((chains R).map f)).1.comp y.1 h at hβ`.

Establish `hw : δ m n (-(m.negOnePow • (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp β (zero_add m))) = 0`. Rewrite using `[δ_neg, δ_units_smul, δ_ofHom_comp, hβ]`. Simplify using the standard rewrite rules. Use `⟨CohomologyClass.mk (Cocycle.mk _ n (by omega) hw), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) _ (zero_add m)) = _`.

Rewrite using `[eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]`. Use `⟨m - 1, by omega, (mappingCone.inl ((chains R).map f)).comp β (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[δ_comp _ _ _ 0 n m (by omega) (by omega) (by omega), mappingCone.δ_inl, hβ]`. Express the relevant statement in the definitionally equal form `_ = y.1 - (Cochain.ofHom ((chains R).map f)).comp _ (zero_add m)`. Simplify using `[Cochain.ofHom_comp]`.
-/
theorem range_of_bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (y : H R U F m) (hy : bd R F f m n h y = 0) :
    ∃ w, pull R f F m w = y := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ y h) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)] at hy
  obtain ⟨β, hβ⟩ := hy
  change δ m n β = (mappingCone.fst ((chains R).map f)).1.comp y.1 h at hβ
  have hw : δ m n (-(m.negOnePow • (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp β (zero_add m))) = 0 := by
    rw [δ_neg, δ_units_smul, δ_ofHom_comp, hβ]; simp
  refine ⟨CohomologyClass.mk (Cocycle.mk _ n (by omega) hw), ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) _ (zero_add m)) = _
  rw [eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m - 1, by omega, (mappingCone.inl ((chains R).map f)).comp β (by omega), ?_⟩
  rw [δ_comp _ _ _ 0 n m (by omega) (by omega) (by omega), mappingCone.δ_inl, hβ]
  change _ = y.1 - (Cochain.ofHom ((chains R).map f)).comp _ (zero_add m)
  simp [Cochain.ofHom_comp]

/- English proof (translation)
Take `⟨y, rfl⟩` from `y.mk_surjective`. Use `congrArg CohomologyClass.mk (Cocycle.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Cochain.ofHom (rmap R f f' u e comm)).comp ((mappingCone.fst ((chains R).map f)).1.comp y.1 h) (zero_add n) = (mappingCone.fst ((chains R).map f')).1.comp ((Cochain.ofHom ((chains R).map u)).comp y.1 (zero_add m)) h`. Rewrite using `[mappingCone.ext_cochain_from_iff _ m n (by omega)]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← Cochain.comp_assoc_of_second_is_zero_cochain]`. Simplify using `[rmap, mappingCone.map]`. Rewrite using `[← Cochain.comp_assoc_of_first_is_zero_cochain]`. Simplify using `[rmap, mappingCone.map]`.
-/
theorem rpull_bd {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f)
    (m n : ℤ) (h : 1 + m = n) (y : H R U F m) :
    rpull R f f' u e comm F n (bd R F f m n h y) = bd R F f' m n h (pull R u F m y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (rmap R f f' u e comm)).comp ((mappingCone.fst ((chains R).map f)).1.comp y.1 h) (zero_add n) =
    (mappingCone.fst ((chains R).map f')).1.comp ((Cochain.ofHom ((chains R).map u)).comp y.1 (zero_add m)) h
  rw [mappingCone.ext_cochain_from_iff _ m n (by omega)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
    simp [rmap, mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
    simp [rmap, mappingCone.map]

/- English proof (translation)
Substitute `hu he` using the available equality. Establish `key : rmap R f f'' (u' ≫ u) (e' ≫ e) comm2 = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm`. Simplify using `only [rmap, Functor.map_comp]`. Conclude with `mappingCone.map_comp ..`. Take `⟨z, rfl⟩` from `z.mk_surjective`.

Use `congrArg CohomologyClass.mk (Cocycle.ext ?_)` and prove the remaining obligations. Simplify using `[zcomp, key, Cochain.ofHom_comp]`.
-/
theorem rpull_comp {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f') (u2 : U'' ⟶ U) (e2 : E'' ⟶ E)
    (comm2 : f'' ≫ e2 = u2 ≫ f) (hu : u2 = u' ≫ u) (he : e2 = e' ≫ e) (n : ℤ) (z : Hrel R f F n) :
    rpull R f f'' u2 e2 comm2 F n z = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n z) := by
  subst hu he
  have key : rmap R f f'' (u' ≫ u) (e' ≫ e) comm2 = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
    simp only [rmap, Functor.map_comp]
    exact mappingCone.map_comp ..
  obtain ⟨z, rfl⟩ := z.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, key, Cochain.ofHom_comp]

end LateralTheory.E.KernelLocalization
