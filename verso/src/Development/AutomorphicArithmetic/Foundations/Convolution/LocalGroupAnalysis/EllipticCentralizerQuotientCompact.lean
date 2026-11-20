import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open PositivityTheory.Rg.Tf.Geo
open NumberField IsDedekindDomain Matrix Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup
open PositivityTheory.Rg.Tf.Core
open scoped NumberField.AdeleRing Pointwise

private def krylovMatrixOfRowVector {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun k => x ᵥ* M ^ (k : ℕ)

/- English proof (translation)
Rewrite using `[Matrix.vecMul_sum, Matrix.vecMul_eq_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.vecMul_smul]`. Both sides reduce to the same expression.
-/
private theorem vecMul_krylov {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x c : Fin n → R) :
    c ᵥ* krylovMatrixOfRowVector M x = x ᵥ* ∑ k : Fin n, c k • M ^ (k : ℕ) := by
  rw [Matrix.vecMul_sum, Matrix.vecMul_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.vecMul_smul]
  rfl

/- English proof (translation)
Use extensionality with `k j`. Establish `: (krylovMatrixOfRowVector M x * t) k j = ((x ᵥ* M ^ (k : ℕ)) ᵥ* t) j` using `rfl`. Rewrite using `[this, vecMul_vecMul, (h.pow_left k).eq, ← vecMul_vecMul]`. Both sides reduce to the same expression.
-/
private theorem krylov_mul_commute {R : Type*} [CommRing R] {n : ℕ} {M t : Matrix (Fin n) (Fin n) R} (h : Commute M t)
    (x : Fin n → R) : krylovMatrixOfRowVector M x * t = krylovMatrixOfRowVector M (x ᵥ* t) := by
  ext k j
  have : (krylovMatrixOfRowVector M x * t) k j = ((x ᵥ* M ^ (k : ℕ)) ᵥ* t) j := rfl
  rw [this, vecMul_vecMul, (h.pow_left k).eq, ← vecMul_vecMul]
  rfl

/- English proof (translation)
Use extensionality with `k j`. Establish `h : (M.map f) ^ (k : ℕ) = (M ^ (k : ℕ)).map f`. Simplify using `using (map_pow f.mapMatrix M k).symm`. Express the relevant statement in the definitionally equal form `f ((x ᵥ* M ^ (k : ℕ)) j) = ((f ∘ x) ᵥ* (M.map f) ^ (k : ℕ)) j`. Rewrite using `[h, RingHom.map_vecMul]`.
-/
private theorem krylov_map_alt {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : (krylovMatrixOfRowVector M x).map f = krylovMatrixOfRowVector (M.map f) (f ∘ x) := by
  ext k j
  have h : (M.map f) ^ (k : ℕ) = (M ^ (k : ℕ)).map f := by
    simpa using (map_pow f.mapMatrix M k).symm
  change f ((x ᵥ* M ^ (k : ℕ)) j) = ((f ∘ x) ᵥ* (M.map f) ^ (k : ℕ)) j
  rw [h, RingHom.map_vecMul]

/- English proof (translation)
Introduce `h0`. Take `⟨c, hc, hc0⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Rewrite `hc0` using `[vecMul_krylov]`. Use `set p : F[X] := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp`. Establish `hpa : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ)`.

Simplify using `[hp, map_sum, Algebra.smul_def]`. Establish `hdeg : p.degree < n` using `degree_sum_fin_lt c`. Establish `hp0 : p ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Use `congrArg (fun q : F[X] => q.coeff k) h` as an intermediate fact. Simplify `this` using `[hp, finsetSum_coeff, coeff_X_pow, Fin.val_inj]`. Establish `hnd : ¬ M.charpoly ∣ p`. Introduce `hd`.

Use `degree_le_of_dvd hd hp0` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`. Conclude with `absurd hdeg (not_lt.2 this)`. Take `⟨a, b, hab⟩` from `(hM.coprime_iff_not_dvd).2 hnd`. Establish `h1` using `congrArg (aeval M) hab`.

Rewrite `h1` using `[map_add, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, mul_comm b p, map_mul, map_one, hpa]`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← vecMul_one x, ← h1, ← vecMul_vecMul, hc0, zero_vecMul]`.
-/
private theorem krylov_det_ne_zero {F : Type*} [Field F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : Irreducible M.charpoly) {x : Fin n → F} (hx : x ≠ 0) : (krylovMatrixOfRowVector M x).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  rw [vecMul_krylov] at hc0
  set p : F[X] := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp
  have hpa : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ) := by
    simp [hp, map_sum, Algebra.smul_def]
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hp0 : p ≠ 0 := by
    intro h
    apply hc
    funext k
    have := congrArg (fun q : F[X] => q.coeff k) h
    simpa [hp, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using this
  have hnd : ¬ M.charpoly ∣ p := by
    intro hd
    have := degree_le_of_dvd hd hp0
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
    exact absurd hdeg (not_lt.2 this)
  obtain ⟨a, b, hab⟩ := (hM.coprime_iff_not_dvd).2 hnd
  have h1 := congrArg (aeval M) hab
  rw [map_add, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, mul_comm b p, map_mul, map_one, hpa] at h1
  apply hx
  rw [← vecMul_one x, ← h1, ← vecMul_vecMul, hc0, zero_vecMul]

/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Use `set c : Fin n → R := (x ᵥ* t) ᵥ* (↑u⁻¹ : Matrix (Fin n) (Fin n) R) with hc`. Use `set q : Matrix (Fin n) (Fin n) R := ∑ k : Fin n, c k • M ^ (k : ℕ) with hq`. Establish `h1 : x ᵥ* q = x ᵥ* t`. Rewrite using `[hq, ← vecMul_krylov, hc, ← hu, vecMul_vecMul, Units.inv_mul, vecMul_one]`.

Establish `hMq : Commute M q` using `Commute.sum_right _ _ _ fun k _ => ((Commute.refl M).pow_right k).smul_right _`. Establish `h2 : t = q`. Establish `: (u : Matrix (Fin n) (Fin n) R) * t = u * q`. Rewrite using `[hu, krylov_mul_commute ht, krylov_mul_commute hMq, h1]`. Conclude with `(Units.mul_right_inj u).1 this`.

Rewrite using `[h2]`. Conclude with `Commute.sum_right _ _ _ fun k _ => (hs.symm.pow_right k).smul_right _`.
-/
private theorem commute_of_krylov_unit {R : Type*} [CommRing R] {n : ℕ} {M s t : Matrix (Fin n) (Fin n) R} {x : Fin n → R}
    (hx : IsUnit (krylovMatrixOfRowVector M x)) (hs : Commute M s) (ht : Commute M t) : Commute s t := by
  obtain ⟨u, hu⟩ := hx
  set c : Fin n → R := (x ᵥ* t) ᵥ* (↑u⁻¹ : Matrix (Fin n) (Fin n) R) with hc
  set q : Matrix (Fin n) (Fin n) R := ∑ k : Fin n, c k • M ^ (k : ℕ) with hq
  have h1 : x ᵥ* q = x ᵥ* t := by
    rw [hq, ← vecMul_krylov, hc, ← hu, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hMq : Commute M q :=
    Commute.sum_right _ _ _ fun k _ => ((Commute.refl M).pow_right k).smul_right _
  have h2 : t = q := by
    have : (u : Matrix (Fin n) (Fin n) R) * t = u * q := by
      rw [hu, krylov_mul_commute ht, krylov_mul_commute hMq, h1]
    exact (Units.mul_right_inj u).1 this
  rw [h2]
  exact Commute.sum_right _ _ _ fun k _ => (hs.symm.pow_right k).smul_right _

/- English proof (translation)
Take `⟨b, hb, k, hk, rfl⟩` from `exists_adelicBorel_mul_maxCompact g`. Establish `hk1` using `mem_normOneGL.1 (maxCompact_le_normOneGL hk)`. Establish `hu` using `isUnit_apply_self_of_mem_adelicBorel hb`. Establish `hdet : AdelicGLn.det K n b = ∏ i, (hu i).unit`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]`. Both sides reduce to the same expression. Rewrite using `[map_mul, map_mul, Positive.val_mul, hk1, mul_one, hdet, map_prod, coe_finset_prod_pos]`. Use `Finset.prod_le_prod (fun i _ => (ideleModule K (hu i).unit).2.le) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk, ← adelicNorm_single_units i]`.

Establish `he : (Pi.single i (((hu i).unit : IdeleGroup K) : 𝔸[K]) : Fin n → 𝔸[K]) = (((hu i).unit : IdeleGroup K) : 𝔸[K]) • (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])`. Rewrite using `[← Pi.single_smul', smul_eq_mul, mul_one]`. Establish `key` using `adelicNorm_le_of_local ((hasFiniteContent_single_one (K := K) i).smul (hu i).unit) ((hasFiniteContent_single_one (K := K) i).vecMul b) (fun _ => 1) (fun _ => 1) ∅ (fun w => ?_) (fun _ _ => rfl) (fun v => ?_)`. Rewrite using `[he]`. Simplify using `using key`.

Rewrite using `[one_mul, infComp_smul, euclidNorm_smul]`. Establish `h1 : euclidNorm (infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])) = 1`. Rewrite using `[← euclidNorm_pi_single_one (E := w.Completion) i]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[infComp]`. Simplify using `[infComp, Pi.single_eq_of_ne hj]`. Both sides reduce to the same expression.

Rewrite using `[h1, mul_one, single_one_vecMul]`. Conclude with `norm_le_euclidNorm (infComp w ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i`. Rewrite using `[one_mul, finComp_smul, norm_smul]`. Establish `h1 : ‖finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])‖ = 1`. Rewrite using `[← norm_pi_single_one (E := v.adicCompletion K) i]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[finComp]`.

Simplify using `[finComp, Pi.single_eq_of_ne hj]`. Both sides reduce to the same expression. Rewrite using `[h1, mul_one, single_one_vecMul]`. Conclude with `norm_le_pi_norm (finComp v ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i`.
-/
private theorem adelic_hadamard_inequality {K : Type*} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤
      ∏ i, adelicNorm ((Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  classical
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact g
  have hk1 := mem_normOneGL.1 (maxCompact_le_normOneGL hk)
  have hu := isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det K n b = ∏ i, (hu i).unit := by
    refine Units.ext ?_
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    rfl
  rw [map_mul, map_mul, Positive.val_mul, hk1, mul_one, hdet, map_prod, coe_finset_prod_pos]
  refine Finset.prod_le_prod (fun i _ => (ideleModule K (hu i).unit).2.le) fun i _ => ?_
  rw [Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk, ← adelicNorm_single_units i]
  have he : (Pi.single i (((hu i).unit : IdeleGroup K) : 𝔸[K]) : Fin n → 𝔸[K]) =
      (((hu i).unit : IdeleGroup K) : 𝔸[K]) • (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have key := adelicNorm_le_of_local ((hasFiniteContent_single_one (K := K) i).smul (hu i).unit)
    ((hasFiniteContent_single_one (K := K) i).vecMul b) (fun _ => 1) (fun _ => 1) ∅ (fun w => ?_)
    (fun _ _ => rfl) (fun v => ?_)
  · rw [he]
    simpa using key
  · rw [one_mul, infComp_smul, euclidNorm_smul]
    have h1 : euclidNorm (infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])) = 1 := by
      rw [← euclidNorm_pi_single_one (E := w.Completion) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [infComp]
      · simp [infComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_euclidNorm (infComp w ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i
  · rw [one_mul, finComp_smul, norm_smul]
    have h1 : ‖finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])‖ = 1 := by
      rw [← norm_pi_single_one (E := v.adicCompletion K) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [finComp]
      · simp [finComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_pi_norm (finComp v ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i

/- English proof (translation)
Establish `hE : IsCompact ((fun y : G => y * γ * y⁻¹) '' D)` using `hD.image (by fun_prop)`. Establish `hcl : IsClosed (Γ : Set G)` using `Subgroup.isClosed_of_discrete`. Establish `hfin : ((fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G)).Finite`. Establish `h1 : IsCompact (Subtype.val ⁻¹' ((fun y : G => y * γ * y⁻¹) '' D) : Set Γ)` using `hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hE`. Use `(h1.finite_of_discrete.image Subtype.val).subset ?_` and prove the remaining obligations.

Introduce and unpack `z ⟨hz, hzΓ⟩`. Conclude with `⟨⟨z, hzΓ⟩, hz, rfl⟩`. Establish `hr : ∀ δ : G, ∃ r ∈ Γ, (∃ g ∈ Γ, g⁻¹ * γ * g = δ) → r⁻¹ * γ * r = δ` using `fun δ => by`. Distinguish the cases in `hδ : ∃ g ∈ Γ, g⁻¹ * γ * g = δ`. Take `⟨g, hg, hg'⟩` from `hδ`.

Conclude with `⟨g, hg, fun _ => hg'⟩`. Conclude with `⟨1, one_mem _, fun h => absurd h hδ⟩`. Use `choose r hrΓ hr using hr`. Establish `hC : IsCompact (⋃ δ ∈ (fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G), (fun y => r δ * y) '' D)` using `hfin.isCompact_biUnion fun δ _ => hD.image (by fun_prop)`. Establish `hZ : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G)`.

Establish `: ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {x | x * γ = γ * x}`. Use extensionality with `x`. Conclude with `Subgroup.mem_centralizer_singleton_iff`. Rewrite using `[this]`. Conclude with `isClosed_eq (by fun_prop) (by fun_prop)`.

Use `⟨Subtype.val ⁻¹' _, hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun t => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, y, hy, hty⟩` from `h t`. Establish `ht : (t : G) * γ = γ * t` using `Subgroup.mem_centralizer_singleton_iff.1 t.2`. Establish `hδ : g⁻¹ * γ * g = y * γ * y⁻¹`. Rewrite `ht` using `[hty]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hr1` using `hr _ ⟨g, hg, hδ⟩`. Use `set ρ := r (y * γ * y⁻¹) with hρ`. Establish `hz : g * ρ⁻¹ ∈ Subgroup.centralizer {γ}`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨_, hz⟩, mul_mem hg (inv_mem (hrΓ _)), (⟨_, hz⟩ : Subgroup.centralizer {γ})⁻¹ * t, ?_, by group⟩` and prove the remaining obligations. Use `Set.mem_biUnion (x := y * γ * y⁻¹) ⟨⟨y, hy, rfl⟩, ?_⟩ ⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hδ]`. Conclude with `mul_mem (mul_mem (inv_mem hg) hγ) hg`.

Express the relevant statement in the definitionally equal form `ρ * y = (g * ρ⁻¹)⁻¹ * (t : G)`. Rewrite using `[hty]`. Use `group`.
-/
private theorem centralizer_compact_fundamental {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {γ : G} (hγ : γ ∈ Γ) {D : Set G} (hD : IsCompact D)
    (h : ∀ t : Subgroup.centralizer {γ}, ∃ g ∈ Γ, ∃ y ∈ D, (t : G) = g * y) :
    ∃ C : Set (Subgroup.centralizer {γ}), IsCompact C ∧ ∀ t : Subgroup.centralizer {γ},
      ∃ g : Subgroup.centralizer {γ}, (g : G) ∈ Γ ∧ ∃ y ∈ C, t = g * y := by
  classical
  have hE : IsCompact ((fun y : G => y * γ * y⁻¹) '' D) := hD.image (by fun_prop)
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hfin : ((fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G)).Finite := by
    have h1 : IsCompact (Subtype.val ⁻¹' ((fun y : G => y * γ * y⁻¹) '' D) : Set Γ) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hE
    refine (h1.finite_of_discrete.image Subtype.val).subset ?_
    rintro z ⟨hz, hzΓ⟩
    exact ⟨⟨z, hzΓ⟩, hz, rfl⟩
  have hr : ∀ δ : G, ∃ r ∈ Γ, (∃ g ∈ Γ, g⁻¹ * γ * g = δ) → r⁻¹ * γ * r = δ := fun δ => by
    by_cases hδ : ∃ g ∈ Γ, g⁻¹ * γ * g = δ
    · obtain ⟨g, hg, hg'⟩ := hδ
      exact ⟨g, hg, fun _ => hg'⟩
    · exact ⟨1, one_mem _, fun h => absurd h hδ⟩
  choose r hrΓ hr using hr
  have hC : IsCompact (⋃ δ ∈ (fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G), (fun y => r δ * y) '' D) :=
    hfin.isCompact_biUnion fun δ _ => hD.image (by fun_prop)
  have hZ : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G) := by
    have : ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {x | x * γ = γ * x} := by
      ext x
      exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  refine ⟨Subtype.val ⁻¹' _, hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun t => ?_⟩
  obtain ⟨g, hg, y, hy, hty⟩ := h t
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have hδ : g⁻¹ * γ * g = y * γ * y⁻¹ := by
    rw [hty] at ht
    calc g⁻¹ * γ * g = g⁻¹ * (γ * (g * y)) * y⁻¹ := by group
      _ = y * γ * y⁻¹ := by rw [← ht]; group
  have hr1 := hr _ ⟨g, hg, hδ⟩
  set ρ := r (y * γ * y⁻¹) with hρ
  have hz : g * ρ⁻¹ ∈ Subgroup.centralizer {γ} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * ρ⁻¹ * γ = g * (ρ⁻¹ * γ * ρ) * ρ⁻¹ := by group
      _ = γ * (g * ρ⁻¹) := by rw [hr1, ← hδ]; group
  refine ⟨⟨_, hz⟩, mul_mem hg (inv_mem (hrΓ _)), (⟨_, hz⟩ : Subgroup.centralizer {γ})⁻¹ * t, ?_, by group⟩
  refine Set.mem_biUnion (x := y * γ * y⁻¹) ⟨⟨y, hy, rfl⟩, ?_⟩ ⟨y, hy, ?_⟩
  · rw [← hδ]
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  · change ρ * y = (g * ρ⁻¹)⁻¹ * (t : G)
    rw [hty]; group

/- English proof (translation)
Introduce `F _ _ n γ γ₁ hγ hirr`. Use `set M : Matrix (Fin n) (Fin n) 𝔸[F] := Units.val (AdelicGLn.diagonal F n γ) with hM`. Establish `hcom : ∀ t : Subgroup.centralizer {γ₁}, Commute M (((t : G1 F n) : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F])` using `fun t => by`. Establish `ht : (t : G1 F n) * γ₁ = γ₁ * t` using `Subgroup.mem_centralizer_singleton_iff.1 t.2`. Use `congrArg (fun z : G1 F n => ((z : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F])) ht` as an intermediate fact.

Simplify using `only [Subgroup.coe_mul, Units.val_mul, hγ] at this`. Conclude with `this.symm`. Establish `hK : ∀ x : Fin n → F, x ≠ 0 → ∃ κ : GL (Fin n) F, ((AdelicGLn.diagonal F n κ : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) = krylovMatrixOfRowVector M (ratVec x)` using `fun x hx => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (krylov_det_ne_zero hirr hx), krylov_map_alt (algebraMap F 𝔸[F]) _ x⟩`. Establish `hn : 0 < n`. Use `hirr.natDegree_pos` as an intermediate fact.

Rewrite `this` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `s t`. Take `⟨κ, hκ⟩` from `hK (Pi.single ⟨0, hn⟩ 1) (by simp)`. Use `commute_of_krylov_unit (hκ ▸ Units.isUnit _) (hcom s) (hcom t)` as an intermediate fact.

Conclude with `Subtype.ext (Subtype.ext (Units.ext this.eq))`. Take `⟨P, hP, hPle⟩` from `exists_adelicNorm_vecMul_le_mul (Set.finite_range fun k : Fin n => AdelicGLn.diagonal F n γ ^ (k : ℕ)).isCompact`. Take `⟨D, hD, hD'⟩` from `exists_isCompact_forall_of_pos_le_height (K := F) (n := n) (inv_pos.2 hP)`. Use `centralizer_compact_fundamental (Gam F n) (show (γ₁ : AdelicGLn.AdelicGL F n) ∈ AdelicGLn.rationalGL F n from ⟨γ, hγ.symm⟩) (isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hD) fun t => ?_` and prove the remaining obligations. Use `set τ : AdelicGLn.AdelicGL F n := ((t : G1 F n) : AdelicGLn.AdelicGL F n) with hτ`.

Establish `hτ1 : τ ∈ normOneGL F n` using `(t : G1 F n).2`. Establish `hht : ∀ x : Fin n → F, x ≠ 0 → P⁻¹ ≤ height τ x` using `fun x hx => by`. Take `⟨κ, hκ⟩` from `hK x hx`. Establish `h1` using `adelic_hadamard_inequality (AdelicGLn.diagonal F n κ * τ)`. Rewrite `h1` using `[mem_normOneGL.1 (mul_mem (rationalGL_le_normOneGL ⟨κ, rfl⟩) hτ1), Units.val_mul, hκ, krylov_mul_commute (hcom t)]`.

Establish `h2 : ∏ i : Fin n, adelicNorm ((Pi.single i (1 : 𝔸[F]) : Fin n → 𝔸[F]) ᵥ* krylovMatrixOfRowVector M (ratVec x ᵥ* (τ : Matrix (Fin n) (Fin n) 𝔸[F]))) ≤ ∏ _i : Fin n, P * height τ x`. Use `Finset.prod_le_prod (fun _ _ => adelicNorm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Use `hPle _ ⟨i, rfl⟩ _ (hasFiniteContent_height τ hx)` as an intermediate fact. Rewrite using `[single_one_vecMul]`. Rewrite `this` using `[Units.val_pow_eq_pow_val]`.

Conclude with `this`. Rewrite `h2` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `h3 : 1 ≤ P * height τ x` using `(one_le_pow_iff_of_nonneg (mul_nonneg hP.le (height_nonneg _ _)) hn.ne').1 (h1.trans h2)`. Rewrite using `[inv_le_iff_one_le_mul₀' hP]`. Conclude with `h3`.

Take `⟨g, hg, y, hy, hgy⟩` from `hD' τ hτ1 hht`. Establish `hg1 : g ∈ normOneGL F n` using `rationalGL_le_normOneGL hg`. Establish `hy1 : y ∈ normOneGL F n`. Establish `: y = g⁻¹ * τ` using `by rw [← hgy, inv_mul_cancel_left]`. Rewrite using `[this]`.

Conclude with `mul_mem (inv_mem hg1) hτ1`. Conclude with `⟨⟨g, hg1⟩, hg, ⟨y, hy1⟩, hy, Subtype.ext hgy.symm⟩`.
-/
theorem UpperTheory.ConvolutionTheory.G.elliptic_centralizer_quotient_compact :
    N4 := by
  intro F _ _ n γ γ₁ hγ hirr
  set M : Matrix (Fin n) (Fin n) 𝔸[F] := Units.val (AdelicGLn.diagonal F n γ) with hM
  have hcom : ∀ t : Subgroup.centralizer {γ₁},
      Commute M (((t : G1 F n) : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) := fun t => by
    have ht : (t : G1 F n) * γ₁ = γ₁ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have := congrArg (fun z : G1 F n => ((z : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F])) ht
    simp only [Subgroup.coe_mul, Units.val_mul, hγ] at this
    exact this.symm
  have hK : ∀ x : Fin n → F, x ≠ 0 → ∃ κ : GL (Fin n) F,
      ((AdelicGLn.diagonal F n κ : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) =
        krylovMatrixOfRowVector M (ratVec x) := fun x hx =>
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (krylov_det_ne_zero hirr hx),
      krylov_map_alt (algebraMap F 𝔸[F]) _ x⟩
  have hn : 0 < n := by
    have := hirr.natDegree_pos
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  constructor
  · intro s t
    obtain ⟨κ, hκ⟩ := hK (Pi.single ⟨0, hn⟩ 1) (by simp)
    have := commute_of_krylov_unit (hκ ▸ Units.isUnit _) (hcom s) (hcom t)
    exact Subtype.ext (Subtype.ext (Units.ext this.eq))
  obtain ⟨P, hP, hPle⟩ := exists_adelicNorm_vecMul_le_mul
    (Set.finite_range fun k : Fin n => AdelicGLn.diagonal F n γ ^ (k : ℕ)).isCompact
  obtain ⟨D, hD, hD'⟩ := exists_isCompact_forall_of_pos_le_height (K := F) (n := n) (inv_pos.2 hP)
  refine centralizer_compact_fundamental (Gam F n) (show (γ₁ : AdelicGLn.AdelicGL F n) ∈ AdelicGLn.rationalGL F n from ⟨γ, hγ.symm⟩)
    (isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hD) fun t => ?_
  set τ : AdelicGLn.AdelicGL F n := ((t : G1 F n) : AdelicGLn.AdelicGL F n) with hτ
  have hτ1 : τ ∈ normOneGL F n := (t : G1 F n).2
  have hht : ∀ x : Fin n → F, x ≠ 0 → P⁻¹ ≤ height τ x := fun x hx => by
    obtain ⟨κ, hκ⟩ := hK x hx
    have h1 := adelic_hadamard_inequality (AdelicGLn.diagonal F n κ * τ)
    rw [mem_normOneGL.1 (mul_mem (rationalGL_le_normOneGL ⟨κ, rfl⟩) hτ1), Units.val_mul, hκ,
      krylov_mul_commute (hcom t)] at h1
    have h2 : ∏ i : Fin n, adelicNorm ((Pi.single i (1 : 𝔸[F]) : Fin n → 𝔸[F]) ᵥ*
        krylovMatrixOfRowVector M (ratVec x ᵥ* (τ : Matrix (Fin n) (Fin n) 𝔸[F]))) ≤ ∏ _i : Fin n, P * height τ x := by
      refine Finset.prod_le_prod (fun _ _ => adelicNorm_nonneg _) fun i _ => ?_
      have := hPle _ ⟨i, rfl⟩ _ (hasFiniteContent_height τ hx)
      rw [single_one_vecMul]
      rw [Units.val_pow_eq_pow_val] at this
      exact this
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : 1 ≤ P * height τ x :=
      (one_le_pow_iff_of_nonneg (mul_nonneg hP.le (height_nonneg _ _)) hn.ne').1 (h1.trans h2)
    rw [inv_le_iff_one_le_mul₀' hP]
    exact h3
  obtain ⟨g, hg, y, hy, hgy⟩ := hD' τ hτ1 hht
  have hg1 : g ∈ normOneGL F n := rationalGL_le_normOneGL hg
  have hy1 : y ∈ normOneGL F n := by
    have : y = g⁻¹ * τ := by rw [← hgy, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hg1) hτ1
  exact ⟨⟨g, hg1⟩, hg, ⟨y, hy1⟩, hy, Subtype.ext hgy.symm⟩
