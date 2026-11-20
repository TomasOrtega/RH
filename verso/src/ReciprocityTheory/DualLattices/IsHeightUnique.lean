import ReciprocityTheory.DualLattices.HtLinStatement
import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

/- English proof (translation)
The claim follows from `Subtype.ext (AlgHom.ext h)`.
-/
lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hnat, -⟩` from `hB1`. Introduce `v`. Take `⟨z, hz, hze⟩` from `H v`. Use `⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hnat _ _ f N _ _ z hz`.

Establish `hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker`. Introduce `a ha`. Rewrite `ha`, the goal using `[Submodule.restrictScalars_mem, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Dq.π.1 (f.1 a) = 0`. Rewrite using `[hfπ, ha, map_zero]`.

Establish `e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk)`. Rewrite using `[← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]`. Use `congr 2`. Conclude with `Subtype.ext hfη`. Establish `e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y)`.

Establish `hc : f.comp Dp.σ = Dq.σ.comp g` using `lhom_ext fun x => hfσ x`. Rewrite using `[← B.map_comp, ← B.map_comp, hc]`. Rewrite `h1` using `[e1, e2]`. Conclude with `h1`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe, hze, map_add, map_one, map_mul, hfσ, hfη]`.

Both sides reduce to the same expression.
-/
lemma isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩
  · have h1 := hnat _ _ f N _ _ z hz
    have hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker := by
      intro a ha
      rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
      change Dq.π.1 (f.1 a) = 0
      rw [hfπ, ha, map_zero]
    have e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk) := by
      rw [← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext hfη
    have e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y) := by
      have hc : f.comp Dp.σ = Dq.σ.comp g := lhom_ext fun x => hfσ x
      rw [← B.map_comp, ← B.map_comp, hc]
    rw [e1, e2] at h1
    exact h1
  · simp only [Units.coe_map, MonoidHom.coe_coe, hze, map_add, map_one, map_mul, hfσ, hfη]
    rfl

/- English proof (translation)
Rewrite using `[← map_nsmul, ← tmul_smul]`. Establish `: N • Dp.ηk = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `N • Dp.η = 0`. Rewrite using `[nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]`.

Rewrite using `[this, tmul_zero, map_zero]`.
-/
lemma nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, hNp⟩` from `hB1`. Introduce `v`. Take `⟨z, hz, hze⟩` from `H v`. Use `⟨z, ?_, hze⟩` and prove the remaining obligations. Establish `h1` using `hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz`.

Rewrite `h1` using `[← map_nsmul]`. Then use the resulting hypothesis.
-/
lemma isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by
  obtain ⟨-, -, -, -, -, -, -, hNp⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨z, ?_, hze⟩
  have h1 := hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz
  rwa [← map_nsmul] at h1

/- English proof (translation)
The claim follows from `((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'`.
-/
lemma isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'

/- English proof (translation)
The claim follows from `((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists`.
-/
lemma isHeight_exists (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃ h, B.IsHeight Dp N y h :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists

/- English proof (translation)
The claim follows from `(heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'`.
-/
lemma isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'

/- English proof (translation)
Take `⟨h, hh⟩` from `B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)`. Establish `h2` using `B.isHeight_add hB1 Dp N hN hh hh`. Rewrite `h2` using `[add_zero]`. Establish `h3` using `B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2`. Establish `h4 : h = 0`.

Use `congrArg (fun k => k - h) h3` as an intermediate fact. Simplify using `using this.symm`. Rewrite `hh` using `[h4]`. Then use the resulting hypothesis.
-/
lemma isHeight_zero (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh

/- English proof (translation)
Take `⟨h', hh'⟩` from `B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])`. Establish `h2` using `B.isHeight_add hB1 Dp N hN H hh'`. Rewrite `h2` using `[add_neg_cancel]`. Establish `h3` using `B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)`. Establish `h4 : h' = -h` using `by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3`.

Rewrite `hh'` using `[h4]`. Then use the resulting hypothesis.
-/
lemma isHeight_neg (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'

/- English proof (translation)
Establish `hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using B.isHeight_zero hB1 Dp N hN`. Consider the case `succ m ih => rw [succ_nsmul, succ_nsmul]`.

Conclude with `B.isHeight_add hB1 Dp N hN ih H`. Break down `k with m | m` into its components or cases. Simplify using `using hnat m`. Establish `hm : N • ((m + 1) • y) = 0` using `by rw [smul_comm, hy, smul_zero]`. Use `B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))` as an intermediate fact.

Simplify `this` using `[negSucc_zsmul]`.
-/
lemma isHeight_zsmul (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using B.isHeight_zero hB1 Dp N hN`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `B.isHeight_add hB1 Dp N hN (H a) ih`.
-/
lemma isHeight_sum (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih

end BX

end ReciprocityTheory.PGsh
