import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open Polynomial UpperTheory.V.W

namespace UpperTheory.Reformulated.B.DeterminantIdentities

/- English proof (translation)
Establish `key : ∀ (e : ℕ) (y₁ y₂ z : MonoidAlgebra B Γ), ∃ z', (1 - T ^ (e + 1) • Φ y₁) * (1 - T ^ (e + 1) • Φ y₂ - T ^ (e + 2) • Φ z') = 1 - T ^ (e + 1) • Φ (y₁ + y₂) - T ^ (e + 2) • Φ z`. Introduce `e y₁ y₂ z`. Establish `h0 : (T ^ (e + 1) • Φ y₁) ^ N = 0`. Rewrite using `[_root_.smul_pow, ← pow_mul, mul_comm, pow_mul, pow_succ, mul_smul, ← one_mul (Φ y₁ ^ N), ← smul_mul_assoc, hT, zero_mul, smul_zero]`. Establish `h1 : (1 - T ^ (e + 1) • Φ y₁) * Φ (∑ k ∈ Finset.range N, (T ^ (e + 1) • y₁) ^ k) = 1`.

Simplify using `only [map_sum, map_pow, map_smul]`. Rewrite using `[mul_neg_geom_sum, h0, sub_zero]`. Use `⟨(∑ k ∈ Finset.range N, (T ^ (e + 1) • y₁) ^ k) * (z + T ^ e • (y₁ * y₂)), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sub, mul_smul_comm, map_mul, ← mul_assoc, h1, one_mul]`. Simplify using `only [map_add, map_smul, map_mul, mul_sub, sub_mul, mul_one, one_mul, smul_add, smul_smul, smul_mul_smul_comm, ← pow_add]`.

Rewrite using `[show e + 2 + e = e + 1 + (e + 1) by ring]`. Normalize the expressions using the abelian group laws. Establish `main : ∀ k e, N ≤ e + k → ∀ y, d (1 - T ^ (e + 1) • Φ y) ∈ S`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `e he y`. Take `⟨c, hc⟩ : ∃ c, e + 1 = c + N` from `⟨e + 1 - N, by omega⟩`. Rewrite using `[hc, pow_add, mul_smul, ← one_mul (Φ y), ← smul_mul_assoc, hT, zero_mul, smul_zero, sub_zero, map_one]`. Conclude with `one_mem _`.

Consider the case `succ k ih`. Introduce `e he`. Establish `h2 : ∀ y z, d (1 - T ^ (e + 1) • Φ y - T ^ (e + 2) • Φ z) ∈ S`. Introduce `y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero`. Introduce `z`. Simplify using `using ih (e + 1) (by omega) z`. Consider the case `add a b ha hb`. Introduce `z`.

Take `⟨z', hz⟩` from `key e a b z`. Rewrite using `[← hz, map_mul]`. Conclude with `mul_mem (by simpa using ha 0) (hb z')`. Consider the case `single g r`. Introduce `z`.

Take `⟨z', hz⟩` from `key e (MonoidAlgebra.single g r) 0 z`. Rewrite `hz` using `[add_zero]`. Rewrite using `[← hz, map_mul]`. Use `mul_mem ?_ (by simpa using ih (e + 1) (by omega) z')` and prove the remaining obligations. Rewrite using `[← map_smul, MonoidAlgebra.smul_single]`.

Conclude with `h _ _`. Introduce `y`. Simplify using `using h2 y 0`. Introduce `y`. Simplify using `using main N 0 (by omega) y`.
-/
private theorem core1 {B Γ F A : Type} [CommRing B] [Monoid Γ] [Ring F] [Algebra B F] [Monoid A]
    (Φ : MonoidAlgebra B Γ →ₐ[B] F) (d : F →* A) (S : Submonoid A) (T : B) (N : ℕ)
    (hT : T ^ N • (1 : F) = 0) (h : ∀ g c, d (1 - Φ (MonoidAlgebra.single g c)) ∈ S) :
    ∀ y, d (1 - T • Φ y) ∈ S := by
  have key : ∀ (e : ℕ) (y₁ y₂ z : MonoidAlgebra B Γ), ∃ z', (1 - T ^ (e + 1) • Φ y₁) *
      (1 - T ^ (e + 1) • Φ y₂ - T ^ (e + 2) • Φ z') =
        1 - T ^ (e + 1) • Φ (y₁ + y₂) - T ^ (e + 2) • Φ z := by
    intro e y₁ y₂ z
    have h0 : (T ^ (e + 1) • Φ y₁) ^ N = 0 := by
      rw [_root_.smul_pow, ← pow_mul, mul_comm, pow_mul, pow_succ, mul_smul, ← one_mul (Φ y₁ ^ N),
        ← smul_mul_assoc, hT, zero_mul, smul_zero]
    have h1 : (1 - T ^ (e + 1) • Φ y₁) * Φ (∑ k ∈ Finset.range N, (T ^ (e + 1) • y₁) ^ k) = 1 := by
      simp only [map_sum, map_pow, map_smul]
      rw [mul_neg_geom_sum, h0, sub_zero]
    refine ⟨(∑ k ∈ Finset.range N, (T ^ (e + 1) • y₁) ^ k) * (z + T ^ e • (y₁ * y₂)), ?_⟩
    rw [mul_sub, mul_smul_comm, map_mul, ← mul_assoc, h1, one_mul]
    simp only [map_add, map_smul, map_mul, mul_sub, sub_mul, mul_one, one_mul, smul_add, smul_smul,
      smul_mul_smul_comm, ← pow_add]
    rw [show e + 2 + e = e + 1 + (e + 1) by ring]
    abel
  have main : ∀ k e, N ≤ e + k → ∀ y, d (1 - T ^ (e + 1) • Φ y) ∈ S := by
    intro k
    induction k with
    | zero =>
      intro e he y
      obtain ⟨c, hc⟩ : ∃ c, e + 1 = c + N := ⟨e + 1 - N, by omega⟩
      rw [hc, pow_add, mul_smul, ← one_mul (Φ y), ← smul_mul_assoc, hT, zero_mul, smul_zero, sub_zero,
        map_one]
      exact one_mem _
    | succ k ih =>
      intro e he
      have h2 : ∀ y z, d (1 - T ^ (e + 1) • Φ y - T ^ (e + 2) • Φ z) ∈ S := by
        intro y
        induction y using MonoidAlgebra.induction_linear with
        | zero =>
          intro z
          simpa using ih (e + 1) (by omega) z
        | add a b ha hb =>
          intro z
          obtain ⟨z', hz⟩ := key e a b z
          rw [← hz, map_mul]
          exact mul_mem (by simpa using ha 0) (hb z')
        | single g r =>
          intro z
          obtain ⟨z', hz⟩ := key e (MonoidAlgebra.single g r) 0 z
          rw [add_zero] at hz
          rw [← hz, map_mul]
          refine mul_mem ?_ (by simpa using ih (e + 1) (by omega) z')
          rw [← map_smul, MonoidAlgebra.smul_single]
          exact h _ _
      intro y
      simpa using h2 y 0
  intro y
  simpa using main N 0 (by omega) y

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, ← coe_eval₂RingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply, eval₂_sub, eval₂_mul] <;> ring`.
-/
private theorem det_one_sub {n : ℕ} {C A : Type} [CommRing C] [CommRing A] (ψ : C →+* A) (c : A)
    (M : Matrix (Fin n) (Fin n) C) :
    (1 - c • M.map ψ).det = eval₂ ψ c M.charpolyRev := by
  rw [Matrix.charpolyRev, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, eval₂_sub, eval₂_mul] <;> ring

/- English proof (translation)
Consider the cases of `subsingleton_or_nontrivial C`. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Set `A'` to `AdjoinRoot (X ^ (n + 1) : C[X])`. Set `α : P[X] →+* A'` to `(AdjoinRoot.mk _).comp (mapRingHom φ)`. Set `ι : C →+* A'` to `AdjoinRoot.of _`.

Use `letI : Algebra P[X] A' := α.toAlgebra`. Establish `hα : ∀ (c : P[X]) (M : Matrix (Fin n) (Fin n) A'), c • M = α c • M` using `fun c M => rfl`. Establish `hC : α.comp Polynomial.C = ι.comp φ`. Use extensionality with `a`. Simplify using `[α, ι]`.

Set `Φ : MonoidAlgebra P[X] Γ →ₐ[P[X]] Matrix (Fin n) (Fin n) A'` to `MonoidAlgebra.lift P[X] _ Γ ((ι.comp (algebraMap A C)).mapMatrix.toMonoidHom.comp ρ)`. Establish `hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = α c • ((ρ g).map (algebraMap A C)).map ι`. Introduce `g c`. Rewrite using `[← hα]`. Simplify using `[Φ]`.

Establish `h1` using `core1 Φ Matrix.detMonoidHom (MonoidHom.mrange α.toMonoidHom) X (n + 1) (by rw [hα]; simp [α]) (by`. Introduce `g c`. Take `⟨p, hp⟩` from `h g`. Rewrite `hp` using `[← Matrix.charpoly_map]`. Use `⟨eval₂ Polynomial.C c (reflect ((ρ g).map (algebraMap A C)).charpoly.natDegree p), ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ]`. Express the relevant statement in the definitionally equal form `α _ = Matrix.det _`. Rewrite using `[det_one_sub, ← Matrix.reverse_charpoly, reverse, hom_eval₂, hC, ← eval₂_map, ← reflect_map, hp])`. Use the proof step `(MonoidAlgebra.mapRingHom Γ Polynomial.C x)`. Establish `h2 : Φ (MonoidAlgebra.mapRingHom Γ Polynomial.C x) = (GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x)).map ι` using `by clear h1`.

Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb, Matrix.map_add ι (map_add ι)]`. Consider the case `single g r`. Rewrite using `[MonoidAlgebra.mapRingHom_single, hΦ]`.

Use extensionality with `i j`. Simplify using `[GDet.repAlg, α, ι]`. Take `⟨p, hp⟩` from `h1`. Express the relevant statement in the definitionally equal form `∃ b, φ b = Matrix.det (GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x))`. Generalize the expression as in `GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x) = M at h2 ⊢`.

Rewrite `hp` using `[h2, hα]`. Express the relevant statement in the definitionally equal form `α p = Matrix.det _ at hp`. Rewrite `hp` using `[det_one_sub]`. Establish `h3 : AdjoinRoot.mk (X ^ (n + 1) : C[X]) (p.map φ) = AdjoinRoot.mk _ M.charpolyRev`. Use `hp.trans ?_` and prove the remaining obligations.

Simplify using `only [α, ι, RingHom.comp_apply, coe_mapRingHom, map_X, AdjoinRoot.mk_X]`. Rewrite using `[← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]`. Establish `h4` using `X_pow_dvd_iff.1 (AdjoinRoot.mk_eq_mk.1 h3) n (by omega)`. Rewrite `h4` using `[coeff_sub, sub_eq_zero, coeff_map, ← Matrix.reverse_charpoly, coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, revAt_le le_rfl, Nat.sub_self]`. Use `⟨(-1) ^ n * p.coeff n, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, ← h4]`. Simplify using the standard rewrite rules.
-/
private theorem core2 {n : ℕ} {P A C Γ : Type} [CommRing P] [CommRing A] [CommRing C] [Algebra A C]
    [Group Γ] (φ : P →+* C) (ρ : Γ →* Matrix (Fin n) (Fin n) A)
    (h : ∀ g, ∃ p : P[X], p.map φ = (ρ g).charpoly.map (algebraMap A C)) (x : MonoidAlgebra P Γ) :
    ∃ b, φ b = (GDet.ofRep ρ).D C (MonoidAlgebra.mapRingHom Γ φ x) := by
  cases subsingleton_or_nontrivial C
  · exact ⟨0, Subsingleton.elim _ _⟩
  let A' := AdjoinRoot (X ^ (n + 1) : C[X])
  let α : P[X] →+* A' := (AdjoinRoot.mk _).comp (mapRingHom φ)
  let ι : C →+* A' := AdjoinRoot.of _
  letI : Algebra P[X] A' := α.toAlgebra
  have hα : ∀ (c : P[X]) (M : Matrix (Fin n) (Fin n) A'), c • M = α c • M := fun c M => rfl
  have hC : α.comp Polynomial.C = ι.comp φ := by
    ext a
    simp [α, ι]
  let Φ : MonoidAlgebra P[X] Γ →ₐ[P[X]] Matrix (Fin n) (Fin n) A' :=
    MonoidAlgebra.lift P[X] _ Γ ((ι.comp (algebraMap A C)).mapMatrix.toMonoidHom.comp ρ)
  have hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = α c • ((ρ g).map (algebraMap A C)).map ι := by
    intro g c
    rw [← hα]
    simp [Φ]
  have h1 := core1 Φ Matrix.detMonoidHom (MonoidHom.mrange α.toMonoidHom) X (n + 1)
    (by rw [hα]; simp [α]) (by
      intro g c
      obtain ⟨p, hp⟩ := h g
      rw [← Matrix.charpoly_map] at hp
      refine ⟨eval₂ Polynomial.C c (reflect ((ρ g).map (algebraMap A C)).charpoly.natDegree p), ?_⟩
      rw [hΦ]
      change α _ = Matrix.det _
      rw [det_one_sub, ← Matrix.reverse_charpoly, reverse, hom_eval₂, hC, ← eval₂_map, ← reflect_map, hp])
    (MonoidAlgebra.mapRingHom Γ Polynomial.C x)
  have h2 : Φ (MonoidAlgebra.mapRingHom Γ Polynomial.C x) =
      (GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x)).map ι := by
    clear h1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, Matrix.map_add ι (map_add ι)]
    | single g r =>
      rw [MonoidAlgebra.mapRingHom_single, hΦ]
      ext i j
      simp [GDet.repAlg, α, ι]
  obtain ⟨p, hp⟩ := h1
  change ∃ b, φ b = Matrix.det (GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x))
  generalize GDet.repAlg ρ C (MonoidAlgebra.mapRingHom Γ φ x) = M at h2 ⊢
  rw [h2, hα] at hp
  change α p = Matrix.det _ at hp
  rw [det_one_sub] at hp
  have h3 : AdjoinRoot.mk (X ^ (n + 1) : C[X]) (p.map φ) = AdjoinRoot.mk _ M.charpolyRev := by
    refine hp.trans ?_
    simp only [α, ι, RingHom.comp_apply, coe_mapRingHom, map_X, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  have h4 := X_pow_dvd_iff.1 (AdjoinRoot.mk_eq_mk.1 h3) n (by omega)
  rw [coeff_sub, sub_eq_zero, coeff_map, ← Matrix.reverse_charpoly, coeff_reverse,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, revAt_le le_rfl, Nat.sub_self] at h4
  refine ⟨(-1) ^ n * p.coeff n, ?_⟩
  rw [Matrix.det_eq_sign_charpoly_coeff, ← h4]
  simp

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, MonoidAlgebra.mapDomain_add, ha, hb]`. Consider the case `single g r => simp`.
-/
private theorem map_dom {B C H G : Type} [CommRing B] [CommRing C] [Group H] [Group G] (f : B →+* C)
    (s : G → H) (x : MonoidAlgebra B G) :
    MonoidAlgebra.mapRingHom H f (x.mapDomain s) = (MonoidAlgebra.mapRingHom G f x).mapDomain s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, MonoidAlgebra.mapDomain_add, ha, hb]
  | single g r => simp

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [MonoidAlgebra.mapDomain_add, ha, hb]`. Consider the case `single g r => simp`.
-/
private theorem dom_dom {C H G K : Type} [CommRing C] (s : G → H) (t : H → K) (x : MonoidAlgebra C G) :
    (x.mapDomain s).mapDomain t = x.mapDomain (t ∘ s) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [MonoidAlgebra.mapDomain_add, ha, hb]
  | single g r => simp

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [MonoidAlgebra.mapDomain_add, ha, hb]`. Consider the case `single g r => simp`.
-/
private theorem dom_id {C G : Type} [CommRing C] (x : MonoidAlgebra C G) : x.mapDomain id = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [MonoidAlgebra.mapDomain_add, ha, hb]
  | single g r => simp

/- English proof (translation)
Establish `hs' : π ∘ s = id` using `funext hs`. Use `⟨⟨fun C _ _ => ⟨⟨fun y => R.D C (y.mapDomain s), ?_⟩, fun x y => ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `h C 1` as an intermediate fact. Rewrite `this` using `[← dom_dom, MonoidAlgebra.mapDomain_one]`. Rewrite using `[this, map_one]`.

Use `h C (x.mapDomain s * y.mapDomain s)` as an intermediate fact. Rewrite `this` using `[← dom_dom, MonoidAlgebra.mapDomain_mul, dom_dom s, dom_dom s, hs', dom_id, dom_id]`. Simplify using `only [this, map_mul]`. Introduce `C C' _ _ _ _ f x`. Express the relevant statement in the definitionally equal form `R.D C' _ = f (R.D C _)`.

Rewrite using `[← R.nat, map_dom]`. Introduce `C _ _ c x`. Express the relevant statement in the definitionally equal form `R.D C _ = _ * R.D C _`. Rewrite using `[← R.homog]`. Use `congr 1`.

Use `ext1`. Simplify using `[Finsupp.mapDomain_smul]`. Use extensionality with `C _ _ x`. Express the relevant statement in the definitionally equal form `R.D C ((x.mapDomain π).mapDomain s) = _`. Rewrite using `[dom_dom, h]`.
-/
private theorem lemA {n : ℕ} {A H G : Type} [CommRing A] [Group H] [Group G] (R : GDet n A H)
    (π : H →* G) (s : G → H) (hs : ∀ g, π (s g) = g)
    (h : ∀ (C : Type) [CommRing C] [Algebra A C] (x : MonoidAlgebra C H),
      R.D C (x.mapDomain (s ∘ π)) = R.D C x) :
    ∃ R' : GDet n A G, R'.comap π = R := by
  have hs' : π ∘ s = id := funext hs
  refine ⟨⟨fun C _ _ => ⟨⟨fun y => R.D C (y.mapDomain s), ?_⟩, fun x y => ?_⟩, ?_, ?_⟩, ?_⟩
  · have := h C 1
    rw [← dom_dom, MonoidAlgebra.mapDomain_one] at this
    rw [this, map_one]
  · have := h C (x.mapDomain s * y.mapDomain s)
    rw [← dom_dom, MonoidAlgebra.mapDomain_mul, dom_dom s, dom_dom s, hs', dom_id, dom_id] at this
    simp only [this, map_mul]
  · intro C C' _ _ _ _ f x
    change R.D C' _ = f (R.D C _)
    rw [← R.nat, map_dom]
  · intro C _ _ c x
    change R.D C _ = _ * R.D C _
    rw [← R.homog]
    congr 1
    ext1
    simp [Finsupp.mapDomain_smul]
  · ext C _ _ x
    change R.D C ((x.mapDomain π).mapDomain s) = _
    rw [dom_dom, h]

private noncomputable def gen (B : Type) {G : Type} [CommRing B] (s : Finset G) :
    MonoidAlgebra (MvPolynomial G B) G := ∑ g ∈ s, MonoidAlgebra.single g (MvPolynomial.X g)

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [gen, map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']`. Use `split_ifs with hg`. Conclude with `hψ g hg`. Conclude with `(Finsupp.notMem_support_iff.1 fun h => hg (hy h)).symm`.
-/
private theorem map_gen {B C G : Type} [CommRing B] [CommRing C] [Group G] (s : Finset G)
    (ψ : MvPolynomial G B →+* C) (y : MonoidAlgebra C G) (hy : y.coeff.support ⊆ s)
    (hψ : ∀ g ∈ s, ψ (MvPolynomial.X g) = y.coeff g) : MonoidAlgebra.mapRingHom G ψ (gen B s) = y := by
  classical
  ext g
  simp only [gen, map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hg
  · exact hψ g hg
  · exact (Finsupp.notMem_support_iff.1 fun h => hg (hy h)).symm

/- English proof (translation)
Simplify using `only [gen, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']`.
-/
private theorem gen_coeff {B G : Type} [CommRing B] [DecidableEq G] (s : Finset G) (g : G) :
    (gen B s).coeff g = if g ∈ s then MvPolynomial.X g else 0 := by
  simp only [gen, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']

/- English proof (translation)
Use `choose E hE using h`. Establish `hinj` using `fun ι : Type => MvPolynomial.map_injective (σ := ι) f hf`. Establish `k1 : ∀ (ι : Type) (y : MonoidAlgebra (MvPolynomial ι B) G) (s : Finset G), y.coeff.support ⊆ s → E ι y = MvPolynomial.aeval y.coeff (E G (gen B s))`. Introduce `ι y s hs`. Set `ψ : MvPolynomial G A →ₐ[A] MvPolynomial ι A` to `MvPolynomial.aeval fun g => MvPolynomial.map f (y.coeff g)`.

Establish `hψ : (MvPolynomial.map f).comp (MvPolynomial.aeval (R` using `B) y.coeff).toRingHom = (ψ : MvPolynomial G A →+* MvPolynomial ι A).comp (MvPolynomial.map f) := by`. Apply the tactic sequence `ext <;> simp [ψ]`. Apply `hinj` to reduce the goal to its premises. Use `Eq.trans ?_ (RingHom.congr_fun hψ _).symm` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hE, hE, RingHom.coe_coe, ← R.nat, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, ← hψ, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply, map_gen s _ y hs (by simp)]`.

Establish `k2 : ∀ (C : Type) [CommRing C] [Algebra B C] (ι : Type) (φ : MvPolynomial ι B →ₐ[B] C) (y : MonoidAlgebra (MvPolynomial ι B) G) (x : MonoidAlgebra C G), MonoidAlgebra.mapRingHom G (φ : MvPolynomial ι B →+* C) y = x → MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)) = φ (E …`. Introduce `C _ _ ι φ y x hx`. Establish `hx' : ∀ g, x.coeff g = φ (y.coeff g)` using `fun g => by rw [← hx]; simp`. Establish `hsub : x.coeff.support ⊆ y.coeff.support` using `fun g hg => by`. Rewrite `hg`, the goal using `[Finsupp.mem_support_iff]`.

Introduce `h0`. Conclude with `hg (by rw [hx', h0, map_zero])`. Rewrite using `[k1 ι y _ subset_rfl, k1 G (gen B x.coeff.support) y.coeff.support (fun g hg => by`. Rewrite `hg` using `[Finsupp.mem_support_iff, gen_coeff]`. Conclude with `hsub (by_contra fun h0 => hg (if_neg h0))), ← AlgHom.comp_apply, ← AlgHom.comp_apply]`.

Use `congr 1`. Use extensionality with `g`. Simplify using `only [AlgHom.comp_apply, MvPolynomial.aeval_X, gen_coeff, ← hx']`. Use `split_ifs with hg`. Simplify using the standard rewrite rules.

Rewrite using `[map_zero, Finsupp.notMem_support_iff.1 hg]`. Establish `k3 : ∀ (C : Type) [CommRing C] [Algebra B C], Function.Surjective (MvPolynomial.aeval (R` using `B) (id : C → C)) := fun C _ _ c => ⟨MvPolynomial.X c, by simp⟩`. Establish `k4 : ∀ (C : Type) [CommRing C] [Algebra B C] (x : MonoidAlgebra C G), ∃ y, MonoidAlgebra.mapRingHom G (MvPolynomial.aeval (R` using `B) (id : C → C) : MvPolynomial C B →+* C) y = x := fun C _ _ x => MonoidAlgebra.map_surjective _ (k3 C) x`. Use `⟨⟨fun C _ _ => ⟨⟨fun x => MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)), ?_⟩, fun x y => ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[k2 C C (MvPolynomial.aeval id) 1 1 (map_one _)]`.

Establish `: E C 1 = 1` using `hinj _ (by rw [hE, map_one, map_one, map_one])`. Rewrite using `[this, map_one]`. Take `⟨x', hx⟩` from `k4 C x`. Take `⟨y', hy⟩` from `k4 C y`. Simplify using `only`.

Rewrite using `[k2 C C _ x' x hx, k2 C C _ y' y hy, k2 C C _ (x' * y') (x * y) (by rw [map_mul, hx, hy]), ← map_mul]`. Use `congr 1`. Conclude with `hinj _ (by rw [map_mul, hE, hE, hE, map_mul, map_mul])`. Introduce `C C' _ _ _ _ g x`. Take `⟨x', hx⟩` from `k4 C x`.

Express the relevant statement in the definitionally equal form `MvPolynomial.aeval _ _ = g (MvPolynomial.aeval _ _)`. Rewrite using `[k2 C C _ x' x hx, k2 C' C (g.comp (MvPolynomial.aeval id)) x' _ (by`. Rewrite using `[← hx, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]`. Use the proof step `rfl)]`. Both sides reduce to the same expression.

Introduce `C _ _ c x`. Take `⟨x', hx⟩` from `k4 C x`. Take `⟨c', rfl⟩` from `k3 C c`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval _ _ = _ * (MvPolynomial.aeval _ _)`. Rewrite using `[k2 C C _ x' x hx, k2 C C (MvPolynomial.aeval id) (c' • x') _ (by`.

Rewrite using `[← hx]`. Use `ext`. Use the proof step `simp), ← map_pow, ← map_mul]`. Use `congr 1`. Use `hinj _ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hE, hE, ← R.homog]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Use extensionality with `C _ _ x`.

Use `letI : Algebra B C := ((algebraMap A C).comp f).toAlgebra`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)) = _`. Establish `hψ : (MvPolynomial.aeval (R` using `B) x.coeff).toRingHom = (MvPolynomial.aeval (R := A) x.coeff : MvPolynomial G A →+* C).comp (MvPolynomial.map f) := by`. Apply the tactic sequence `ext <;> simp [RingHom.algebraMap_toAlgebra]`. Use `(RingHom.congr_fun hψ _).trans ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, hE, RingHom.coe_coe, ← R.nat, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, map_gen _ _ x subset_rfl (by simp)]`.
-/
private theorem lemB {n : ℕ} {B A G : Type} [CommRing B] [CommRing A] [Group G] (R : GDet n A G)
    (f : B →+* A) (hf : Function.Injective f)
    (h : ∀ (ι : Type) (x : MonoidAlgebra (MvPolynomial ι B) G), ∃ b, MvPolynomial.map f b =
      R.D (MvPolynomial ι A) (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x)) :
    ∃ D : GDet n B G, D.map f = R := by
  classical
  choose E hE using h
  have hinj := fun ι : Type => MvPolynomial.map_injective (σ := ι) f hf
  have k1 : ∀ (ι : Type) (y : MonoidAlgebra (MvPolynomial ι B) G) (s : Finset G), y.coeff.support ⊆ s →
      E ι y = MvPolynomial.aeval y.coeff (E G (gen B s)) := by
    intro ι y s hs
    let ψ : MvPolynomial G A →ₐ[A] MvPolynomial ι A :=
      MvPolynomial.aeval fun g => MvPolynomial.map f (y.coeff g)
    have hψ : (MvPolynomial.map f).comp (MvPolynomial.aeval (R := B) y.coeff).toRingHom =
        (ψ : MvPolynomial G A →+* MvPolynomial ι A).comp (MvPolynomial.map f) := by
      ext <;> simp [ψ]
    apply hinj
    refine Eq.trans ?_ (RingHom.congr_fun hψ _).symm
    rw [RingHom.comp_apply, hE, hE, RingHom.coe_coe, ← R.nat, ← RingHom.comp_apply,
      ← MonoidAlgebra.mapRingHom_comp, ← hψ, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply,
      map_gen s _ y hs (by simp)]
  have k2 : ∀ (C : Type) [CommRing C] [Algebra B C] (ι : Type) (φ : MvPolynomial ι B →ₐ[B] C)
      (y : MonoidAlgebra (MvPolynomial ι B) G) (x : MonoidAlgebra C G),
      MonoidAlgebra.mapRingHom G (φ : MvPolynomial ι B →+* C) y = x →
      MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)) = φ (E ι y) := by
    intro C _ _ ι φ y x hx
    have hx' : ∀ g, x.coeff g = φ (y.coeff g) := fun g => by rw [← hx]; simp
    have hsub : x.coeff.support ⊆ y.coeff.support := fun g hg => by
      rw [Finsupp.mem_support_iff] at hg ⊢
      intro h0
      exact hg (by rw [hx', h0, map_zero])
    rw [k1 ι y _ subset_rfl, k1 G (gen B x.coeff.support) y.coeff.support (fun g hg => by
      rw [Finsupp.mem_support_iff, gen_coeff] at hg
      exact hsub (by_contra fun h0 => hg (if_neg h0))), ← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext g
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, gen_coeff, ← hx']
    split_ifs with hg
    · simp
    · rw [map_zero, Finsupp.notMem_support_iff.1 hg]
  have k3 : ∀ (C : Type) [CommRing C] [Algebra B C], Function.Surjective
      (MvPolynomial.aeval (R := B) (id : C → C)) := fun C _ _ c => ⟨MvPolynomial.X c, by simp⟩
  have k4 : ∀ (C : Type) [CommRing C] [Algebra B C] (x : MonoidAlgebra C G), ∃ y,
      MonoidAlgebra.mapRingHom G (MvPolynomial.aeval (R := B) (id : C → C) : MvPolynomial C B →+* C) y = x :=
    fun C _ _ x => MonoidAlgebra.map_surjective _ (k3 C) x
  refine ⟨⟨fun C _ _ => ⟨⟨fun x => MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)), ?_⟩,
    fun x y => ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [k2 C C (MvPolynomial.aeval id) 1 1 (map_one _)]
    have : E C 1 = 1 := hinj _ (by rw [hE, map_one, map_one, map_one])
    rw [this, map_one]
  · obtain ⟨x', hx⟩ := k4 C x
    obtain ⟨y', hy⟩ := k4 C y
    dsimp only
    rw [k2 C C _ x' x hx, k2 C C _ y' y hy, k2 C C _ (x' * y') (x * y) (by rw [map_mul, hx, hy]),
      ← map_mul]
    congr 1
    exact hinj _ (by rw [map_mul, hE, hE, hE, map_mul, map_mul])
  · intro C C' _ _ _ _ g x
    obtain ⟨x', hx⟩ := k4 C x
    change MvPolynomial.aeval _ _ = g (MvPolynomial.aeval _ _)
    rw [k2 C C _ x' x hx, k2 C' C (g.comp (MvPolynomial.aeval id)) x' _ (by
      rw [← hx, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]; rfl)]
    rfl
  · intro C _ _ c x
    obtain ⟨x', hx⟩ := k4 C x
    obtain ⟨c', rfl⟩ := k3 C c
    change MvPolynomial.aeval _ _ = _ * (MvPolynomial.aeval _ _)
    rw [k2 C C _ x' x hx, k2 C C (MvPolynomial.aeval id) (c' • x') _ (by
      rw [← hx]; ext; simp), ← map_pow, ← map_mul]
    congr 1
    refine hinj _ ?_
    rw [map_mul, map_pow, hE, hE, ← R.homog]
    congr 1
    ext
    simp
  · ext C _ _ x
    letI : Algebra B C := ((algebraMap A C).comp f).toAlgebra
    change MvPolynomial.aeval x.coeff (E G (gen B x.coeff.support)) = _
    have hψ : (MvPolynomial.aeval (R := B) x.coeff).toRingHom =
        (MvPolynomial.aeval (R := A) x.coeff : MvPolynomial G A →+* C).comp (MvPolynomial.map f) := by
      ext <;> simp [RingHom.algebraMap_toAlgebra]
    refine (RingHom.congr_fun hψ _).trans ?_
    rw [RingHom.comp_apply, hE, RingHom.coe_coe, ← R.nat, ← RingHom.comp_apply,
      ← MonoidAlgebra.mapRingHom_comp, map_gen _ _ x subset_rfl (by simp)]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `q (Matrix.det (GDet.repAlg ρ' C' _)) = Matrix.det (GDet.repAlg ρ C _)`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, MonoidAlgebra.mapDomain_add, ha, hb]`. Consider the case `single g r`. Use extensionality with `i j`. Use `congrFun (congrFun (ht g) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Simplify using `[GDet.repAlg, hq, this]`.
-/
private theorem proj {n : ℕ} {A C C' H Γ : Type} [CommRing A] [CommRing C] [CommRing C'] [Algebra A C]
    [Group H] [Group Γ] (ρ : H →* Matrix (Fin n) (Fin n) A) (ρ' : Γ →* Matrix (Fin n) (Fin n) C')
    (φ : C →+* C') (q : C' →+* C) (hq : ∀ c, q (φ c) = c) (t : Γ → H)
    (ht : ∀ p, (ρ' p).map q = (ρ (t p)).map (algebraMap A C)) (y : MonoidAlgebra C Γ) :
    q ((GDet.ofRep ρ').D C' (MonoidAlgebra.mapRingHom Γ φ y)) = (GDet.ofRep ρ).D C (y.mapDomain t) := by
  change q (Matrix.det (GDet.repAlg ρ' C' _)) = Matrix.det (GDet.repAlg ρ C _)
  rw [RingHom.map_det]
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, MonoidAlgebra.mapDomain_add, ha, hb]
  | single g r =>
    ext i j
    have := congrFun (congrFun (ht g) i) j
    simp only [Matrix.map_apply] at this
    simp [GDet.repAlg, hq, this]

/- English proof (translation)
Set `Γ : Subgroup (H × H)` to `(π.comp (MonoidHom.fst H H)).eqLocus (π.comp (MonoidHom.snd H H))`. Set `ρ' : Γ →* Matrix (Fin n) (Fin n) (C × C)` to `{ toFun := fun p => Matrix.of fun i j => (algebraMap A C (ρ p.1.1 i j), algebraMap A C (ρ p.1.2 i j)) map_one' := by`. Apply the tactic sequence `ext i j <;> by_cases hij : i = j <;> simp [hij, Matrix.one_apply]`. Use the proof step `map_mul' := fun p q => by`. Apply the tactic sequence `ext i j <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum] }`.

Establish `h1 : ∀ p, (ρ' p).map (RingHom.fst C C) = (ρ p.1.1).map (algebraMap A C)` using `fun p => rfl`. Establish `h2 : ∀ p, (ρ' p).map (RingHom.snd C C) = (ρ p.1.2).map (algebraMap A C)` using `fun p => rfl`. Set `φ : C →+* C × C` to `(RingHom.id C).prod (RingHom.id C)`. Set `u : H → Γ` to `fun a => ⟨(a, s (π a)), (hs _).symm⟩`. Take `⟨b, hb⟩` from `core2 (C := C × C) φ ρ' (fun p => ⟨(ρ p.1.1).charpoly.map (algebraMap A C), by`.

Establish `e1` using `Matrix.charpoly_map (ρ' p) (RingHom.fst C C)`. Establish `e2` using `Matrix.charpoly_map (ρ' p) (RingHom.snd C C)`. Rewrite `e1` using `[h1, Matrix.charpoly_map]`. Rewrite `e2` using `[h2, Matrix.charpoly_map, ← h p.1.1 p.1.2 p.2]`. Use extensionality with `k`.

Simplify `congrArg (fun r => r.coeff k) e1` using `[φ]`. Simplify `congrArg (fun r => r.coeff k) e2⟩) (x.mapDomain u)` using `[φ]`. Establish `e1` using `proj ρ ρ' φ (RingHom.fst C C) (fun c => rfl) _ h1 (x.mapDomain u)`. Establish `e2` using `proj ρ ρ' φ (RingHom.snd C C) (fun c => rfl) _ h2 (x.mapDomain u)`. Rewrite `e1`, `e2` using `[← hb, dom_dom]`.

Conclude with `(e2.symm.trans e1).trans (congrArg _ (dom_id x))`.
-/
private theorem invar {n : ℕ} {A H G : Type} [CommRing A] [Group H] [Group G]
    (ρ : H →* Matrix (Fin n) (Fin n) A) (π : H →* G) (s : G → H) (hs : ∀ g, π (s g) = g)
    (h : ∀ a b, π a = π b → (ρ a).charpoly = (ρ b).charpoly)
    (C : Type) [CommRing C] [Algebra A C] (x : MonoidAlgebra C H) :
    (GDet.ofRep ρ).D C (x.mapDomain (s ∘ π)) = (GDet.ofRep ρ).D C x := by
  let Γ : Subgroup (H × H) := (π.comp (MonoidHom.fst H H)).eqLocus (π.comp (MonoidHom.snd H H))
  let ρ' : Γ →* Matrix (Fin n) (Fin n) (C × C) :=
    { toFun := fun p => Matrix.of fun i j => (algebraMap A C (ρ p.1.1 i j), algebraMap A C (ρ p.1.2 i j))
      map_one' := by
        ext i j <;> by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      map_mul' := fun p q => by
        ext i j <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum] }
  have h1 : ∀ p, (ρ' p).map (RingHom.fst C C) = (ρ p.1.1).map (algebraMap A C) := fun p => rfl
  have h2 : ∀ p, (ρ' p).map (RingHom.snd C C) = (ρ p.1.2).map (algebraMap A C) := fun p => rfl
  let φ : C →+* C × C := (RingHom.id C).prod (RingHom.id C)
  let u : H → Γ := fun a => ⟨(a, s (π a)), (hs _).symm⟩
  obtain ⟨b, hb⟩ := core2 (C := C × C) φ ρ' (fun p => ⟨(ρ p.1.1).charpoly.map (algebraMap A C), by
    have e1 := Matrix.charpoly_map (ρ' p) (RingHom.fst C C)
    have e2 := Matrix.charpoly_map (ρ' p) (RingHom.snd C C)
    rw [h1, Matrix.charpoly_map] at e1
    rw [h2, Matrix.charpoly_map, ← h p.1.1 p.1.2 p.2] at e2
    ext k
    · simpa [φ] using congrArg (fun r => r.coeff k) e1
    · simpa [φ] using congrArg (fun r => r.coeff k) e2⟩) (x.mapDomain u)
  have e1 := proj ρ ρ' φ (RingHom.fst C C) (fun c => rfl) _ h1 (x.mapDomain u)
  have e2 := proj ρ ρ' φ (RingHom.snd C C) (fun c => rfl) _ h2 (x.mapDomain u)
  rw [← hb, dom_dom] at e1 e2
  exact (e2.symm.trans e1).trans (congrArg _ (dom_id x))

end UpperTheory.Reformulated.B.DeterminantIdentities

open Polynomial UpperTheory.V.W UpperTheory.Reformulated.B.DeterminantIdentities in
/- English proof (translation)
Introduce `n B A H G _ _ _ _ _ _ _ I _ f hf π hπ hq ρ cp hcp hcont hker`. Establish `hinj` using `Polynomial.map_injective f hf`. Set `K : Subgroup H` to `{ carrier := {k | ∀ h, cp (h * k) = cp h} one_mem' := fun h => by rw [mul_one] mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha] inv_mem' := fun {a} ha h => by rw [← ha (h * a⁻¹), inv_mul_cancel_right] }`. Establish `hK : π.ker ≤ K`. Use `hker K ?_ fun k hk h => hinj (by rw [hcp, hcp, map_mul, MonoidHom.mem_ker.1 hk, mul_one])` and prove the remaining obligations.

Establish `: (K : Set H) = ⋂ (h : H) (j : ℕ) (N : ℕ), {k | Ideal.Quotient.mk (I ^ N) ((cp (h * k)).coeff j) = Ideal.Quotient.mk (I ^ N) ((cp h).coeff j)}`. Use extensionality with `k`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Use `⟨fun hk h j N => by rw [hk h], fun hk h => Polynomial.ext fun j => ?_⟩` and prove the remaining obligations. Use `sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun N => ?_)` and prove the remaining obligations.

Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `Ideal.Quotient.eq.1 (hk h j N)`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun h => isClosed_iInter fun j => isClosed_iInter fun N => ((hcont j N).comp_continuous (continuous_const_mul h)).isClosed_fiber _`. Establish `hch : ∀ a b, π a = π b → (ρ a).charpoly = (ρ b).charpoly` using `fun a b hab => by`.

Rewrite using `[← hcp, ← hcp, ← hK (x := a⁻¹ * b) (by simp [hab]) a, mul_inv_cancel_left]`. Use `choose s hs using hπ`. Take `⟨R, hR⟩` from `lemA (GDet.ofRep ρ) π s hs (invar ρ π s hs hch)`. Establish `hR' : ∀ (C : Type) [CommRing C] [Algebra A C] (x : MonoidAlgebra C H), R.D C (x.mapDomain π) = (GDet.ofRep ρ).D C x` using `fun C _ _ x => by rw [← hR]; rfl`. Take `⟨D, hD⟩` from `lemB R f hf fun ι x => by`.

Take `⟨b, hb⟩` from `core2 (C := MvPolynomial ι A) (MvPolynomial.map f : MvPolynomial ι B →+* _) ρ (fun g => ⟨(cp g).map MvPolynomial.C, by`. Rewrite using `[← hcp, Polynomial.map_map, Polynomial.map_map]`. Use `congr 1`. Use `ext1`. Use the proof step `simp⟩) (x.mapDomain s)`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, ← hR', ← map_dom, dom_dom, show π ∘ s = id from funext hs, dom_id]`. Establish `hchi : ∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g`. Introduce `g`. Apply `hinj` to reduce the goal to its premises.

Use `letI : Algebra B A[X] := ((algebraMap A A[X]).comp f).toAlgebra`. Set `ψ : B[X] →ₐ[B] A[X]` to `{ mapRingHom f with commutes' := fun b => Polynomial.map_C f }`. Establish `e` using `D.nat B[X] A[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (π g) 1))`. Use `e.symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(D.map f).D A[X] _ = _`.

Establish `e2 : MonoidAlgebra.mapRingHom G (ψ : B[X] →+* A[X]) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (π g) 1)) = MonoidAlgebra.mapDomainRingHom A[X] π (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)`. Rewrite using `[map_sub, map_sub]`. Establish `hX : ψ X = X` using `Polynomial.map_X f`. Simplify using `[hX]`. Rewrite using `[hD, e2, hcp]`.

Use `(hR' A[X] _).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.det (GDet.repAlg ρ A[X] _) = Matrix.det _`. Use `congr 1`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases hij : i = j <;> simp [GDet.repAlg, hij, Matrix.charmatrix_apply, Matrix.one_apply]`.

Use `⟨D, ?_, hchi, fun i N U => ?_⟩` and prove the remaining obligations. Rewrite using `[← hR, ← hD]`. Both sides reduce to the same expression. Rewrite using `[← hq.isOpen_preimage, ← Set.preimage_comp]`. Use `(hcont (n - i) N).comp (fun z => (-1) ^ i * z) U` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `[GDet.lam, hchi]`.
-/
theorem UpperTheory.Reformulated.B.DeterminantIdentities.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [inst : CommRing B] [inst_1 : CommRing A] [inst_2 : Group H] [inst_3 : Group G]
      [inst_4 : TopologicalSpace H] [IsTopologicalGroup H] [inst_6 : TopologicalSpace G] (I : Ideal B) [IsHausdorff I B]
      (f : B →+* A),
      Function.Injective (⇑f : B → A) →
        ∀ (π : H →* G),
          Function.Surjective (⇑π : H → G) →
            Topology.IsQuotientMap (⇑π : H → G) →
              ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → Polynomial B),
                (∀ (g : H), Polynomial.map f (cp g) = ((ρ : H → Matrix (Fin n) (Fin n) A) g).charpoly) →
                  (∀ (j : ℕ), UpperTheory.V.Alg.AdicCont I fun (g : H) ↦ (cp g).coeff j) →
                    (∀ (U : Subgroup H), IsClosed (↑U : Set H) → ρ.ker ≤ U → π.ker ≤ U) →
                      ∃ (D : UpperTheory.V.W.GDet n B G),
                        (D.comap π).map f = UpperTheory.V.W.GDet.ofRep ρ ∧
                          (∀ (g : H), D.chi (MonoidAlgebra.single ((π : H → G) g) (1 : B)) = cp g) ∧ D.IsCont I := by
  intro n B A H G _ _ _ _ _ _ _ I _ f hf π hπ hq ρ cp hcp hcont hker
  have hinj := Polynomial.map_injective f hf
  let K : Subgroup H :=
    { carrier := {k | ∀ h, cp (h * k) = cp h}
      one_mem' := fun h => by rw [mul_one]
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha h => by rw [← ha (h * a⁻¹), inv_mul_cancel_right] }
  have hK : π.ker ≤ K := by
    refine hker K ?_ fun k hk h => hinj (by rw [hcp, hcp, map_mul, MonoidHom.mem_ker.1 hk, mul_one])
    have : (K : Set H) = ⋂ (h : H) (j : ℕ) (N : ℕ), {k | Ideal.Quotient.mk (I ^ N) ((cp (h * k)).coeff j) =
        Ideal.Quotient.mk (I ^ N) ((cp h).coeff j)} := by
      ext k
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun hk h j N => by rw [hk h], fun hk h => Polynomial.ext fun j => ?_⟩
      refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun N => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (hk h j N)
    rw [this]
    exact isClosed_iInter fun h => isClosed_iInter fun j => isClosed_iInter fun N =>
      ((hcont j N).comp_continuous (continuous_const_mul h)).isClosed_fiber _
  have hch : ∀ a b, π a = π b → (ρ a).charpoly = (ρ b).charpoly := fun a b hab => by
    rw [← hcp, ← hcp, ← hK (x := a⁻¹ * b) (by simp [hab]) a, mul_inv_cancel_left]
  choose s hs using hπ
  obtain ⟨R, hR⟩ := lemA (GDet.ofRep ρ) π s hs (invar ρ π s hs hch)
  have hR' : ∀ (C : Type) [CommRing C] [Algebra A C] (x : MonoidAlgebra C H),
      R.D C (x.mapDomain π) = (GDet.ofRep ρ).D C x := fun C _ _ x => by rw [← hR]; rfl
  obtain ⟨D, hD⟩ := lemB R f hf fun ι x => by
    obtain ⟨b, hb⟩ := core2 (C := MvPolynomial ι A) (MvPolynomial.map f : MvPolynomial ι B →+* _) ρ
      (fun g => ⟨(cp g).map MvPolynomial.C, by
        rw [← hcp, Polynomial.map_map, Polynomial.map_map]
        congr 1
        ext1
        simp⟩) (x.mapDomain s)
    refine ⟨b, ?_⟩
    rw [hb, ← hR', ← map_dom, dom_dom, show π ∘ s = id from funext hs, dom_id]
  have hchi : ∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g := by
    intro g
    apply hinj
    letI : Algebra B A[X] := ((algebraMap A A[X]).comp f).toAlgebra
    let ψ : B[X] →ₐ[B] A[X] := { mapRingHom f with commutes' := fun b => Polynomial.map_C f }
    have e := D.nat B[X] A[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (π g) 1))
    refine e.symm.trans ?_
    change (D.map f).D A[X] _ = _
    have e2 : MonoidAlgebra.mapRingHom G (ψ : B[X] →+* A[X])
        (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (π g) 1)) =
        MonoidAlgebra.mapDomainRingHom A[X] π (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1) := by
      rw [map_sub, map_sub]
      have hX : ψ X = X := Polynomial.map_X f
      simp [hX]
    rw [hD, e2, hcp]
    refine (hR' A[X] _).trans ?_
    change Matrix.det (GDet.repAlg ρ A[X] _) = Matrix.det _
    congr 1
    ext i j : 2
    by_cases hij : i = j <;> simp [GDet.repAlg, hij, Matrix.charmatrix_apply, Matrix.one_apply]
  refine ⟨D, ?_, hchi, fun i N U => ?_⟩
  · rw [← hR, ← hD]
    rfl
  · rw [← hq.isOpen_preimage, ← Set.preimage_comp]
    have := (hcont (n - i) N).comp (fun z => (-1) ^ i * z) U
    convert this using 2
    ext g
    simp [GDet.lam, hchi]
