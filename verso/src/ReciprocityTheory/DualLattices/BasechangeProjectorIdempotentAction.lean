import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section W2c

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[psiW, red, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
private lemma reducedColumnMap_toZMod {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) (x : Fin r → ℤ_[p]) :
    psiW Bw (fun i => PadicInt.toZMod (x i)) = red p g (Bw *ᵥ x) := by
  funext i
  simp [psiW, red, Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (algebraMap ℤ_[p] R) M t i).symm`.
-/
private lemma map_algebraMap_mulVec_comp {m n : Type} [Fintype n] (M : Matrix m n ℤ_[p]) (t : n → ℤ_[p]) :
    M.map (algebraMap ℤ_[p] R) *ᵥ (algebraMap ℤ_[p] R ∘ t) = algebraMap ℤ_[p] R ∘ (M *ᵥ t) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℤ_[p] R) M t i).symm

private def IsHopfApproximable (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (ℓ : (Fin r → ℤ_[p]) → R) : Prop :=
  ∃ F ∈ H.AA.carrier, ∀ x, ∃ s : R,
    algebraMap R C (ℓ x) - F (red p g (Bw *ᵥ x)) = algebraMap R C ((p : R) * s)

/- English proof (translation)
Take `⟨F, hF, h'⟩` from `hg`. Use `⟨F, hF, fun x => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `h' x`. Conclude with `⟨s, by rw [← h x]; exact hs⟩`.
-/
private lemma isHopfApproximable_congr (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    {ℓ ℓ' : (Fin r → ℤ_[p]) → R} (h : ∀ x, ℓ x = ℓ' x) (hg : IsHopfApproximable H Bw ℓ) : IsHopfApproximable H Bw ℓ' := by
  obtain ⟨F, hF, h'⟩ := hg
  refine ⟨F, hF, fun x => ?_⟩
  obtain ⟨s, hs⟩ := h' x
  exact ⟨s, by rw [← h x]; exact hs⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `⟨0, H.AA.carrier.zero_mem, fun x => ⟨0, ?_⟩⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `insert a S ha ih`.

Take `⟨Fa, hFa, hax⟩` from `h a (Finset.mem_insert_self a S)`. Take `⟨FS, hFS, hSx⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`. Use `⟨c a • Fa + FS, H.AA.carrier.add_mem (H.AA.carrier.smul_mem _ hFa) hFS, fun x => ?_⟩` and prove the remaining obligations. Take `⟨sa, hsa⟩` from `hax x`. Take `⟨sS, hsS⟩` from `hSx x`.

Use `⟨c a * sa + sS, ?_⟩` and prove the remaining obligations. Use `beta_reduce at hsS ⊢`. Rewrite using `[Finset.sum_insert ha]`. Rewrite using `[Pi.add_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def, map_add, map_mul] at hsa hsS ⊢`.

Take the linear combination `(algebraMap R C (c a)) * hsa + hsS`.
-/
private lemma isHopfApproximable_sum (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    {ι : Type} (S : Finset ι) (c : ι → R) (ℓ : ι → (Fin r → ℤ_[p]) → R)
    (h : ∀ i ∈ S, IsHopfApproximable H Bw (ℓ i)) :
    IsHopfApproximable H Bw (fun x => ∑ i ∈ S, c i * ℓ i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, H.AA.carrier.zero_mem, fun x => ⟨0, ?_⟩⟩
    simp
  | insert a S ha ih =>
    obtain ⟨Fa, hFa, hax⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨FS, hFS, hSx⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨c a • Fa + FS, H.AA.carrier.add_mem (H.AA.carrier.smul_mem _ hFa) hFS, fun x => ?_⟩
    obtain ⟨sa, hsa⟩ := hax x
    obtain ⟨sS, hsS⟩ := hSx x
    refine ⟨c a * sa + sS, ?_⟩
    beta_reduce at hsS ⊢
    rw [Finset.sum_insert ha]
    rw [Pi.add_apply, Pi.smul_apply]
    simp only [Algebra.smul_def, map_add, map_mul] at hsa hsS ⊢
    linear_combination (algebraMap R C (c a)) * hsa + hsS

/- English proof (translation)
Take `⟨f, hf, hm⟩` from `h`. Conclude with `⟨f, hf, fun x => hm (Bw *ᵥ x)⟩`.
-/
private lemma isHopfApproximable_comp_mulVec (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (m : TT p g → R)
    (h : ∃ f ∈ H.AA.carrier, ∀ t : TT p g, ∃ r : R,
      algebraMap R C (m t) - f (red p g t) = algebraMap R C ((p : R) * r)) :
    IsHopfApproximable H Bw (fun x => m (Bw *ᵥ x)) := by
  obtain ⟨f, hf, hm⟩ := h
  exact ⟨f, hf, fun x => hm (Bw *ᵥ x)⟩

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← map_mul, horth]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Rewrite using `[map_zero, Matrix.zero_mulVec]`.
-/
private lemma orthogonal_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (w : Fin m) (s : TT p g) (i : Fin m) :
    H.ρ (e i) *ᵥ (H.ρ (e w) *ᵥ s) = if i = w then H.ρ (e w) *ᵥ s else 0 := by
  rw [Matrix.mulVec_mulVec, ← map_mul, horth]
  split_ifs with h
  · subst h
    rfl
  · rw [map_zero, Matrix.zero_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, H.projectors.2.2.2.1 (e w), hPT, Matrix.zero_mulVec]`.
-/
private lemma projector_mul_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (w : Fin m) (s : TT p g) :
    H.P *ᵥ (H.ρ (e w) *ᵥ s) = 0 := by
  rw [Matrix.mulVec_mulVec, H.projectors.2.2.2.1 (e w), hPT, Matrix.zero_mulVec]

/- English proof (translation)
Establish `h0 : (algebraMap ℤ_[p] R ∘ (0 : Ix g → ℤ_[p])) = 0` using `funext fun _ => map_zero _`. Establish `hterm : ∀ i, (H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) = if i = w then H.ρL (e w) *ᵥ (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s))) else 0`. Introduce `i`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, orthogonal_idempotent_action H e horth w s i]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Both sides reduce to the same expression. Rewrite using `[h0, Matrix.mulVec_zero, Matrix.mulVec_zero]`. Establish `hP : (H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) = 0`. Rewrite using `[← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, projector_mul_idempotent_action H e hPT w s, h0, Matrix.mulVec_zero]`.

Unfold `btP`. Rewrite using `[Matrix.add_mulVec, Matrix.sum_mulVec, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hP, add_zero]`.
-/
private lemma basechangeProjector_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (w : Fin m) (s : TT p g) :
    btP H e *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) =
      H.ρL (e w) *ᵥ (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s))) := by
  have h0 : (algebraMap ℤ_[p] R ∘ (0 : Ix g → ℤ_[p])) = 0 := funext fun _ => map_zero _
  have hterm : ∀ i, (H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R)) *ᵥ
      (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) =
      if i = w then H.ρL (e w) *ᵥ (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s))) else 0 := by
    intro i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, orthogonal_idempotent_action H e horth w s i]
    split_ifs with h
    · subst h
      rfl
    · rw [h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hP : (H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) = 0 := by
    rw [← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, projector_mul_idempotent_action H e hPT w s, h0, Matrix.mulVec_zero]
  unfold btP
  rw [Matrix.add_mulVec, Matrix.sum_mulVec, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), hP, add_zero]

/- English proof (translation)
Establish `hx : ∀ x, ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) = phiP H e *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x))` using `fun x => by`. Rewrite using `[← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp]`. Establish `hfix : ∀ x, H.ρ (e w) *ᵥ (Bw *ᵥ x) = Bw *ᵥ x`. Introduce `x`. Establish `hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ (e w)))`.

Rewrite using `[← hrange]`. Conclude with `⟨x, rfl⟩`. Take `⟨s, hs⟩` from `hmem`. Rewrite using `[← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, horth, if_pos rfl]`. Break down `k with j | j` into its components or cases.

Use `isHopfApproximable_congr H Bw (ℓ := fun x => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x))) j) (fun x => ?_) (isHopfApproximable_comp_mulVec H Bw (fun t => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) j) (H.h4 j).1)` and prove the remaining obligations. Rewrite using `[hx, phiP, Matrix.fromRows_mulVec]`. Both sides reduce to the same expression. Use `isHopfApproximable_congr H Bw (ℓ := fun x => ∑ l ∈ Finset.univ, H.ρL (e w) j l * (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ (Bw *ᵥ x)))) l) (fun x => ?_) (isHopfApproximable_sum H Bw Finset.univ (fun l => H.ρL (e w) j l) (fun l x => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ …` and prove the remaining obligations. Rewrite using `[hx, phiP, Matrix.fromRows_mulVec, Sum.elim_inr] conv_rhs => rw [← hfix x]`.

Rewrite using `[basechangeProjector_idempotent_action H e horth hPT w (Bw *ᵥ x)]`. Both sides reduce to the same expression. Take `⟨f, hf, hfapprox⟩` from `(H.h4 l).2`. Take `⟨f', hf', hf'eq⟩` from `H.h3 (e w) f hf`. Use `isHopfApproximable_comp_mulVec H Bw (fun t => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ t))) l) ⟨f', hf', fun t => ?_⟩` and prove the remaining obligations.

Take `⟨r0, hr0⟩` from `hfapprox (H.ρ (e w) *ᵥ t)`. Conclude with `⟨r0, by rw [hf'eq t]; exact hr0⟩`.
-/
private lemma isHopfApproximable_row (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (w : Fin m) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hrange : LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))))
    (k : Fin g ⊕ Fin g) :
    IsHopfApproximable H Bw
      (fun x => ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k) := by
  have hx : ∀ x, ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) =
      phiP H e *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x)) := fun x => by
    rw [← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp]
  have hfix : ∀ x, H.ρ (e w) *ᵥ (Bw *ᵥ x) = Bw *ᵥ x := by
    intro x
    have hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    rw [← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, horth, if_pos rfl]
  rcases k with j | j
  · refine isHopfApproximable_congr H Bw (ℓ := fun x => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x))) j)
      (fun x => ?_) (isHopfApproximable_comp_mulVec H Bw (fun t => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) j) (H.h4 j).1)
    rw [hx, phiP, Matrix.fromRows_mulVec]
    rfl
  · refine isHopfApproximable_congr H Bw
      (ℓ := fun x => ∑ l ∈ Finset.univ, H.ρL (e w) j l *
        (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ (Bw *ᵥ x)))) l)
      (fun x => ?_) (isHopfApproximable_sum H Bw Finset.univ (fun l => H.ρL (e w) j l)
        (fun l x => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ (Bw *ᵥ x)))) l) (fun l _ => ?_))
    · rw [hx, phiP, Matrix.fromRows_mulVec, Sum.elim_inr]
      conv_rhs => rw [← hfix x]
      rw [basechangeProjector_idempotent_action H e horth hPT w (Bw *ᵥ x)]
      rfl
    · obtain ⟨f, hf, hfapprox⟩ := (H.h4 l).2
      obtain ⟨f', hf', hf'eq⟩ := H.h3 (e w) f hf
      refine isHopfApproximable_comp_mulVec H Bw (fun t => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ t))) l)
        ⟨f', hf', fun t => ?_⟩
      obtain ⟨r0, hr0⟩ := hfapprox (H.ρ (e w) *ᵥ t)
      exact ⟨r0, by rw [hf'eq t]; exact hr0⟩

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.mulVecLin Bw)` using `LinearMap.ker_eq_bot.1 hker`. Set `eB` to `LinearEquiv.ofInjective (Matrix.mulVecLin Bw) hinj`. Establish `hQmem : ∀ y, Matrix.mulVecLin Q y ∈ LinearMap.range (Matrix.mulVecLin Bw)` using `fun y => by`. Rewrite using `[hrange]`. Conclude with `⟨y, rfl⟩`.

Set `q` to `(Matrix.mulVecLin Q).codRestrict (LinearMap.range (Matrix.mulVecLin Bw)) hQmem`. Use `⟨LinearMap.toMatrix' (eB.symm.toLinearMap ∘ₗ q), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Establish `hQB : Q *ᵥ (Bw *ᵥ x) = Bw *ᵥ x`. Establish `hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin Q)`.

Rewrite using `[← hrange]`. Conclude with `⟨x, rfl⟩`. Take `⟨s, hs⟩` from `hmem`. Rewrite using `[← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ]`. Establish `hq : q (Bw *ᵥ x) = eB x`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[q, eB, hQB]`. Simplify using `[hq]`.
-/
private lemma exists_leftInverse_of_range_eq {r : ℕ} (Q : Matrix (Ix g) (Ix g) ℤ_[p]) (hQ : Q * Q = Q)
    (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hrange : LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin Q))
    (hker : LinearMap.ker (Matrix.mulVecLin Bw) = ⊥) :
    ∃ M : Matrix (Fin r) (Ix g) ℤ_[p], ∀ x, M *ᵥ (Bw *ᵥ x) = x := by
  classical
  have hinj : Function.Injective (Matrix.mulVecLin Bw) := LinearMap.ker_eq_bot.1 hker
  let eB := LinearEquiv.ofInjective (Matrix.mulVecLin Bw) hinj
  have hQmem : ∀ y, Matrix.mulVecLin Q y ∈ LinearMap.range (Matrix.mulVecLin Bw) := fun y => by
    rw [hrange]
    exact ⟨y, rfl⟩
  let q := (Matrix.mulVecLin Q).codRestrict (LinearMap.range (Matrix.mulVecLin Bw)) hQmem
  refine ⟨LinearMap.toMatrix' (eB.symm.toLinearMap ∘ₗ q), fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have hQB : Q *ᵥ (Bw *ᵥ x) = Bw *ᵥ x := by
    have hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin Q) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    rw [← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ]
  have hq : q (Bw *ᵥ x) = eB x := by
    apply Subtype.ext
    simp [q, eB, hQB]
  simp [hq]

/- English proof (translation)
Use `⟨(fun j => M i j) ᵥ* E⁻¹, fun x => ?_⟩` and prove the remaining obligations. Unfold `pair`. Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul E hE, Matrix.vecMul_one]`. Establish `hx` using `congrFun (hM x) i`. Rewrite using `[← hx]`.

Both sides reduce to the same expression.
-/
private lemma exists_padicPairing_eq_coord {r : ℕ} (E : Matrix (Ix g) (Ix g) ℤ_[p]) (hE : IsUnit E.det)
    (M : Matrix (Fin r) (Ix g) ℤ_[p]) (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hM : ∀ x, M *ᵥ (Bw *ᵥ x) = x) (i : Fin r) :
    ∃ s : TT p g, ∀ x, pair p g E s (Bw *ᵥ x) = x i := by
  refine ⟨(fun j => M i j) ᵥ* E⁻¹, fun x => ?_⟩
  unfold pair
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul E hE, Matrix.vecMul_one]
  have hx := congrFun (hM x) i
  rw [← hx]
  rfl

/- English proof (translation)
Establish `h0 : PadicInt.toZMod (z - ((PadicInt.toZMod z).val : ℤ_[p])) = 0`. Rewrite using `[map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Establish `hmem : z - ((PadicInt.toZMod z).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])}`. Rewrite using `[← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]`. Conclude with `(RingHom.mem_ker).2 h0`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨y, by linear_combination -hy⟩`.
-/
private lemma exists_eq_toZMod_val_add_mul (z : ℤ_[p]) : ∃ y : ℤ_[p], z = ((PadicInt.toZMod z).val : ℤ_[p]) + p * y := by
  have h0 : PadicInt.toZMod (z - ((PadicInt.toZMod z).val : ℤ_[p])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hmem : z - ((PadicInt.toZMod z).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact (RingHom.mem_ker).2 h0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by linear_combination -hy⟩

/- English proof (translation)
Assume the negation of the conclusion as `hp2`. Establish `hp3 : 3 ≤ p`. Use `(Fact.out : p.Prime).two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hcv` using `hS.cp_val`.

Establish `hpne` using `hS.p_ne`. Establish `hplt` using `hS.p_lt`. Generalize the expression as in `v (algebraMap R C cp) = c at hcv h1`. Establish `hc0 : c ≠ 0`. Introduce `hc`.

Apply `hpne` to reduce the goal to its premises. Rewrite using `[← hcv, hc, zero_pow (by omega)]`. Establish `hc1 : c < 1`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Establish `h1c : 1 ≤ c ^ (p - 1)` using `one_le_pow₀ hc`. Rewrite `h1c` using `[hcv]`. Conclude with `absurd hplt (not_lt.2 h1c)`. Establish `hle : c ≤ c ^ (p - 1)`. Rewrite using `[hcv]`.

Conclude with `h1.trans h2`. Establish `hlt : c ^ (p - 1) < c`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sq]`. Conclude with `mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hc0) hc1`.

Conclude with `absurd hle (not_le.2 hlt)`.
-/
private lemma p_eq_two_of_valuation_le (hS : HodgeTateSetting p v R O σ cp) (dj : R)
    (h1 : v (algebraMap R C cp) ≤ v (algebraMap R C dj))
    (h2 : v (algebraMap R C dj) ≤ v (algebraMap R C (p : R))) : p = 2 := by
  by_contra hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hcv := hS.cp_val
  have hpne := hS.p_ne
  have hplt := hS.p_lt
  generalize v (algebraMap R C cp) = c at hcv h1
  have hc0 : c ≠ 0 := by
    intro hc
    apply hpne
    rw [← hcv, hc, zero_pow (by omega)]
  have hc1 : c < 1 := by
    by_contra hc
    push Not at hc
    have h1c : 1 ≤ c ^ (p - 1) := one_le_pow₀ hc
    rw [hcv] at h1c
    exact absurd hplt (not_lt.2 h1c)
  have hle : c ≤ c ^ (p - 1) := by
    rw [hcv]
    exact h1.trans h2
  have hlt : c ^ (p - 1) < c := by
    calc c ^ (p - 1) ≤ c ^ 2 := pow_le_pow_of_le_one zero_le hc1.le (by omega)
      _ < c := by
        rw [sq]
        exact mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hc0) hc1
  exact absurd hle (not_le.2 hlt)

end W2c

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsum hPT hsumL hPTL w hw r Bw hrange hker lam dj hspan hdj`. Establish `hint` using `hS.integers`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hspan`. Establish `hci : ∀ i, ∑ k, c k * (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i = dj * lam i`. Introduce `i`.

Establish `hcf` using `congrFun hc i`. Simplify `hcf` using `[Finset.sum_apply, smul_eq_mul]`. Establish `hp0 : algebraMap R C (p : R) ≠ 0` using `fun h0 => hS.p_ne (by rw [h0, map_zero])`. Establish `hcp0 : v (algebraMap R C cp) ≠ 0`. Introduce `h0`.

Apply `hS.p_ne` to reduce the goal to its premises. Rewrite using `[← hS.cp_val, h0, zero_pow (by have := (Fact.out : p.Prime).two_le; omega)]`. Establish `hdj0 : 0 < v (algebraMap R C dj)` using `lt_of_lt_of_le (pos_iff_ne_zero.2 hcp0) hdj`. Distinguish the cases in `hcase : v (algebraMap R C dj) ≤ v (algebraMap R C (p : R))`. Establish `hp2 : p = 2` using `p_eq_two_of_valuation_le hS dj hdj hcase`.

Establish `hpc : v (algebraMap R C (p : R)) = v (algebraMap R C cp)`. Rewrite using `[← hS.cp_val, hp2]`. Evaluate the numerical expressions. Establish `hvdj : v (algebraMap R C dj) = v (algebraMap R C (p : R))` using `le_antisymm hcase (by rw [hpc]; exact hdj)`. Establish `hQ : H.ρ (e w) * H.ρ (e w) = H.ρ (e w)` using `by rw [← map_mul, horth, if_pos rfl]`.

Take `⟨M, hM⟩` from `exists_leftInverse_of_range_eq (H.ρ (e w)) hQ Bw hrange hker`. Use `choose sv hsv using fun i => exists_padicPairing_eq_coord H.E H.isUnit_det_E M Bw hM i`. Use `choose χ hχ hχv using fun i => H.h5 hp2 (sv i)`. Take `⟨u, hu⟩` from `hint.exists_of_le_one (r := algebraMap R C dj / algebraMap R C (p : R)) (le_of_eq (by rw [Valuation.map_div, hvdj, div_self hS.p_ne]))`. Establish `h2C : algebraMap R C (p : R) = 2`.

Rewrite using `[map_natCast, hp2]`. Evaluate the numerical expressions. Establish `hu2 : algebraMap R C u * 2 = algebraMap R C dj` using `by rw [hu, ← h2C, div_mul_cancel₀ _ hp0]`. Set `F : Nb p g → C` to `∑ i, (u * lam i) • ((1 : Nb p g → C) - χ i)`. Establish `hF : F ∈ H.AA.carrier` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ H.AA.one_mem (hχ i))`.

Use `⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩` and prove the remaining obligations. Use `show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _`. Rewrite using `[reducedColumnMap_toZMod]`. Use `choose y hy using fun i => exists_eq_toZMod_val_add_mul (x i)`. Establish `hFval : F (red p g (Bw *ᵥ x)) = ∑ i, algebraMap R C (dj * lam i * ((PadicInt.toZMod (x i)).val : R))`.

Simplify using `only [F, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, hχv, hsv]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hlt` using `ZMod.val_lt (PadicInt.toZMod (x i))`. Break down `(show (PadicInt.toZMod (x i)).val = 0 ∨ (PadicInt.toZMod (x i)).val = 1 by omega) with h | h` into its components or cases. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Rewrite using `[h, Algebra.smul_def]`. Simplify using `only [pow_one, Nat.cast_one, mul_one, map_mul]`. Rewrite using `[← hu2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hxR : ∀ i, algebraMap ℤ_[p] R (x i) = ((PadicInt.toZMod (x i)).val : R) + (p : R) * algebraMap ℤ_[p] R (y i)`. Introduce `i`. Use `conv_lhs => rw [hy i]`. Simplify using `only [map_add, map_mul, map_natCast]`. Establish `hR : ∑ i, dj * lam i * ((PadicInt.toZMod (x i)).val : R) - dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i) = -(dj * (p : R) * ∑ i, lam i * algebraMap ℤ_[p] R (y i))`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hxR i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hFval, ← map_sum, ← map_sub, hR, map_neg, Valuation.map_neg]`.

Simplify using `only [map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at hcase`. Take `⟨F, hF, hFx⟩` from `isHopfApproximable_sum H Bw Finset.univ c (fun k x => ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k) (fun k _ => isHopfApproximable_row H e horth hPT w Bw hrange k)`. Use `⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs⟩` from `hFx x`. Establish `hlin : ∑ k, c k * ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k = dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i)`. Simplify using `only [Matrix.mulVec, dotProduct, Function.comp_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← hci i, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hs' : F (red p g (Bw *ᵥ x)) - algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i)) = -algebraMap R C ((p : R) * s)`. Rewrite using `[← hlin, ← hs]`.

Expand and normalize the polynomial expressions, which then agree. Use `show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _`. Rewrite using `[reducedColumnMap_toZMod, hs', Valuation.map_neg, map_mul, Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem restrictedHopfOrderApproximation : RestrictedHopfOrderApproximationStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsum hPT hsumL hPTL w hw r Bw hrange hker
    lam dj hspan hdj
  have hint := hS.integers
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hspan
  have hci : ∀ i, ∑ k, c k * (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i = dj * lam i := by
    intro i
    have hcf := congrFun hc i
    simpa [Finset.sum_apply, smul_eq_mul] using hcf
  have hp0 : algebraMap R C (p : R) ≠ 0 := fun h0 => hS.p_ne (by rw [h0, map_zero])
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    apply hS.p_ne
    rw [← hS.cp_val, h0, zero_pow (by have := (Fact.out : p.Prime).two_le; omega)]
  have hdj0 : 0 < v (algebraMap R C dj) := lt_of_lt_of_le (pos_iff_ne_zero.2 hcp0) hdj
  by_cases hcase : v (algebraMap R C dj) ≤ v (algebraMap R C (p : R))
  · have hp2 : p = 2 := p_eq_two_of_valuation_le hS dj hdj hcase
    have hpc : v (algebraMap R C (p : R)) = v (algebraMap R C cp) := by
      rw [← hS.cp_val, hp2]
      norm_num
    have hvdj : v (algebraMap R C dj) = v (algebraMap R C (p : R)) :=
      le_antisymm hcase (by rw [hpc]; exact hdj)
    have hQ : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, horth, if_pos rfl]
    obtain ⟨M, hM⟩ := exists_leftInverse_of_range_eq (H.ρ (e w)) hQ Bw hrange hker
    choose sv hsv using fun i => exists_padicPairing_eq_coord H.E H.isUnit_det_E M Bw hM i
    choose χ hχ hχv using fun i => H.h5 hp2 (sv i)
    obtain ⟨u, hu⟩ := hint.exists_of_le_one (r := algebraMap R C dj / algebraMap R C (p : R))
      (le_of_eq (by rw [Valuation.map_div, hvdj, div_self hS.p_ne]))
    have h2C : algebraMap R C (p : R) = 2 := by
      rw [map_natCast, hp2]
      norm_num
    have hu2 : algebraMap R C u * 2 = algebraMap R C dj := by rw [hu, ← h2C, div_mul_cancel₀ _ hp0]
    let F : Nb p g → C := ∑ i, (u * lam i) • ((1 : Nb p g → C) - χ i)
    have hF : F ∈ H.AA.carrier := Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.sub_mem _ H.AA.one_mem (hχ i))
    refine ⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩
    show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _
    rw [reducedColumnMap_toZMod]
    choose y hy using fun i => exists_eq_toZMod_val_add_mul (x i)
    have hFval : F (red p g (Bw *ᵥ x)) =
        ∑ i, algebraMap R C (dj * lam i * ((PadicInt.toZMod (x i)).val : R)) := by
      simp only [F, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, hχv, hsv]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hlt := ZMod.val_lt (PadicInt.toZMod (x i))
      rcases (show (PadicInt.toZMod (x i)).val = 0 ∨ (PadicInt.toZMod (x i)).val = 1 by omega) with h | h
      · rw [h]
        simp
      · rw [h, Algebra.smul_def]
        simp only [pow_one, Nat.cast_one, mul_one, map_mul]
        rw [← hu2]
        ring
    have hxR : ∀ i, algebraMap ℤ_[p] R (x i) =
        ((PadicInt.toZMod (x i)).val : R) + (p : R) * algebraMap ℤ_[p] R (y i) := by
      intro i
      conv_lhs => rw [hy i]
      simp only [map_add, map_mul, map_natCast]
    have hR : ∑ i, dj * lam i * ((PadicInt.toZMod (x i)).val : R) -
        dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i) =
        -(dj * (p : R) * ∑ i, lam i * algebraMap ℤ_[p] R (y i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hxR i]
      ring
    rw [hFval, ← map_sum, ← map_sub, hR, map_neg, Valuation.map_neg]
    simp only [map_mul]
    calc v (algebraMap R C dj) * v (algebraMap R C (p : R)) *
          v (algebraMap R C (∑ i, lam i * algebraMap ℤ_[p] R (y i)))
        ≤ v (algebraMap R C dj) * v (algebraMap R C (p : R)) * 1 :=
          mul_le_mul_of_nonneg_left (hint.map_le_one _) zero_le
      _ = v (algebraMap R C dj) * v (algebraMap R C (p : R)) := mul_one _
      _ < v (algebraMap R C dj) * 1 := mul_lt_mul_of_pos_left hS.p_lt hdj0
      _ = v (algebraMap R C dj) := mul_one _
  · push Not at hcase
    obtain ⟨F, hF, hFx⟩ := isHopfApproximable_sum H Bw Finset.univ c
      (fun k x => ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k)
      (fun k _ => isHopfApproximable_row H e horth hPT w Bw hrange k)
    refine ⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩
    obtain ⟨s, hs⟩ := hFx x
    have hlin : ∑ k, c k * ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k =
        dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i) := by
      simp only [Matrix.mulVec, dotProduct, Function.comp_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← hci i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hs' : F (red p g (Bw *ᵥ x)) - algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i)) =
        -algebraMap R C ((p : R) * s) := by
      rw [← hlin, ← hs]
      ring
    show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _
    rw [reducedColumnMap_toZMod, hs', Valuation.map_neg, map_mul, Valuation.map_mul]
    calc v (algebraMap R C (p : R)) * v (algebraMap R C s)
        ≤ v (algebraMap R C (p : R)) * 1 := mul_le_mul_of_nonneg_left (hint.map_le_one s) zero_le
      _ = v (algebraMap R C (p : R)) := mul_one _
      _ < v (algebraMap R C dj) := hcase

end ReciprocityTheory.PGsh.Up
