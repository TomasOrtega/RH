import ReciprocityTheory.DualLattices.InstAddCommMonoidFibreFst
import ReciprocityTheory.DualLattices.NilSurjOfSqZero

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `HEq.rfl`.
-/
lemma pmap_congr_hom {S : LAlg R₀} {f g : LHom R S} (h : f = g) {x y : B.G R} (u : B.P R x y) :
    HEq (B.pmap f u) (B.pmap g u) := by
  subst h
  exact HEq.rfl

/- English proof (translation)
Proceed by induction on `Y using TensorProduct.induction_on with`. Consider the case `zero => exact smul_zero _`. Consider the case `tmul g k`. Rewrite using `[← Nat.cast_smul_eq_nsmul R₀, ← TensorProduct.tmul_smul]`. Establish `hk : ((N : R₀) • k) = 0`.

Use `ext`. Simplify using `[Algebra.smul_def, hN]`. Rewrite using `[hk, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, add_zero]`.
-/
lemma nsmul_tensor_eq_zero {A : Type u} [CommRing A] [Algebra R₀ A] {N : ℕ}
    (hN : (N : A) = 0) (K : Submodule R₀ A) (Y : B.gg ⊗[R₀] K) : N • Y = 0 := by
  induction Y using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul g k =>
    rw [← Nat.cast_smul_eq_nsmul R₀, ← TensorProduct.tmul_smul]
    have hk : ((N : R₀) • k) = 0 := by
      ext
      simp [Algebra.smul_def, hN]
    rw [hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/- English proof (translation)
Take `⟨l, hl⟩` from `B.exists_smul u v`. Establish `hπl : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l = 1`. Establish `h1 : B.pmap Dp.π v = B.smul (Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l) (B.pmap Dp.π u)`. Rewrite using `[← hl, B.pmap_smul]`. Establish `h2 : B.pmap Dp.π u = B.pmap Dp.π v` using `eq_of_heq (hu.trans hv.symm)`.

Rewrite `h1` using `[h2]`. Conclude with `B.smul_eq_self h1.symm`. Establish `hπl' : Dp.π.1 (l : (Dp.D : Type u)) = 1`. Use `congrArg Units.val hπl` as an intermediate fact. Simplify using `using this`.

Use `set d : (Dp.D : Type u) := (l : (Dp.D : Type u)) - 1 with hd`. Establish `hdk : Dp.π.1 d = 0` using `by rw [hd, map_sub, hπl', map_one, sub_self]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π d hdk)`. Establish `hdd : d * d = 0`. Rewrite using `[← ha]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hNd : (N : (Dp.D : Type u)) * d = 0`. Rewrite using `[Dp.natCast_D hN, zero_mul]`. Establish `hpow : ∀ n : ℕ, (1 + d) ^ n = 1 + (n : (Dp.D : Type u)) * d`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih]`. Establish `: (1 + (k : (Dp.D : Type u)) * d) * (1 + d) = 1 + ((k : (Dp.D : Type u)) + 1) * d + k * (d * d)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hdd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlN : l ^ N = 1`.

Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, show (l : (Dp.D : Type u)) = 1 + d by rw [hd]; ring, hpow, hNd, add_zero]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hl, B.nsmul1_smul, hlN, B.one_smul]`. Rewrite using `[← hl, B.nsmul2_smul, hlN, B.one_smul]`.
-/
lemma nsmul_of_same_red {N : ℕ} (hN : (N : (R : Type u)) = 0) {x y : B.G Dp.D}
    {x₀ y₀ : B.G R} (e : B.P R x₀ y₀) (u v : B.P Dp.D x y) (hu : HEq (B.pmap Dp.π u) e)
    (hv : HEq (B.pmap Dp.π v) e) : B.nsmul1 u N = B.nsmul1 v N ∧ B.nsmul2 u N = B.nsmul2 v N := by
  obtain ⟨l, hl⟩ := B.exists_smul u v
  have hπl : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l = 1 := by
    have h1 : B.pmap Dp.π v = B.smul (Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l) (B.pmap Dp.π u) := by
      rw [← hl, B.pmap_smul]
    have h2 : B.pmap Dp.π u = B.pmap Dp.π v := eq_of_heq (hu.trans hv.symm)
    rw [h2] at h1
    exact B.smul_eq_self h1.symm
  have hπl' : Dp.π.1 (l : (Dp.D : Type u)) = 1 := by
    have := congrArg Units.val hπl
    simpa using this
  set d : (Dp.D : Type u) := (l : (Dp.D : Type u)) - 1 with hd
  have hdk : Dp.π.1 d = 0 := by rw [hd, map_sub, hπl', map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π d hdk)
  have hdd : d * d = 0 := by
    rw [← ha]
    calc a * Dp.η * (a * Dp.η) = a * a * (Dp.η * Dp.η) := by ring
      _ = 0 := by rw [Dp.η_sq, mul_zero]
  have hNd : (N : (Dp.D : Type u)) * d = 0 := by
    rw [Dp.natCast_D hN, zero_mul]
  have hpow : ∀ n : ℕ, (1 + d) ^ n = 1 + (n : (Dp.D : Type u)) * d := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have : (1 + (k : (Dp.D : Type u)) * d) * (1 + d) = 1 + ((k : (Dp.D : Type u)) + 1) * d + k * (d * d) := by
        ring
      rw [this, hdd]
      push_cast
      ring
  have hlN : l ^ N = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show (l : (Dp.D : Type u)) = 1 + d by rw [hd]; ring, hpow, hNd,
      add_zero]
  constructor
  · rw [← hl, B.nsmul1_smul, hlN, B.one_smul]
  · rw [← hl, B.nsmul2_smul, hlN, B.one_smul]

/- English proof (translation)
Substitute `hx hy` using the available equality. Take `⟨u0⟩` from `B.nonempty Dp.D x y`. Take `⟨l, hl, -⟩` from `B.trans (B.pmap Dp.π u0) e`. Use `⟨B.smul (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) u0, ?_⟩` and prove the remaining obligations. Rewrite using `[B.pmap_smul]`.

Establish `h1 : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) = l`. Use `ext`. Simplify using `[Dp.sect]`. Rewrite using `[h1, hl]`.
-/
lemma exists_lift_red {x y : B.G Dp.D} {x₀ y₀ : B.G R} (hx : B.map Dp.π x = x₀)
    (hy : B.map Dp.π y = y₀) (e : B.P R x₀ y₀) : ∃ u : B.P Dp.D x y, HEq (B.pmap Dp.π u) e := by
  subst hx hy
  obtain ⟨u0⟩ := B.nonempty Dp.D x y
  obtain ⟨l, hl, -⟩ := B.trans (B.pmap Dp.π u0) e
  refine ⟨B.smul (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) u0, ?_⟩
  rw [B.pmap_smul]
  have h1 : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u))
      (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) = l := by
    ext
    simp [Dp.sect]
  rw [h1, hl]

def HtC (N : ℕ) (y : B.G R) (x : B.G Dp.D) (E : (Dp.D : Type u)) : Prop :=
  ∃ v : B.P Dp.D x (B.map Dp.σ y), HEq (B.pmap Dp.π v) (B.zero1 y) ∧
    HEq (B.nsmul1 v N) (B.zero1 (B.map Dp.σ y)) ∧
    ∃ c : (Dp.D : Type u)ˣ, (c : (Dp.D : Type u)) = 1 - E ∧
      HEq (B.nsmul2 v N) (B.smul c (B.zero2 x))

/- English proof (translation)
Substitute `hx hE` using the available equality. Conclude with `id`.
-/
lemma HtC_congr {N : ℕ} {y : B.G R} {x x' : B.G Dp.D} {E E' : (Dp.D : Type u)} (hx : x = x')
    (hE : E = E') : B.HtC Dp N y x E → B.HtC Dp N y x' E' := by
  subst hx hE
  exact id

/- English proof (translation)
Establish `pmap_heq : ∀ {S : LAlg R₀} (f : LHom Dp.D S) {a a' b b' : B.G Dp.D} (ha : a = a') (hb : b = b') {w : B.P Dp.D a b} {w' : B.P Dp.D a' b'}, HEq w w' → HEq (B.pmap f w) (B.pmap f w')`. Introduce `S f a a' b b' ha hb w w' hw`. Substitute `ha hb` using the available equality. Rewrite using `[eq_of_heq hw]`. Establish `tr1h : ∀ {a a' b : B.G Dp.D} (e : a = a') (w : B.P Dp.D a b), HEq (B.tr1 e w) w`.

Introduce `a a' b e w`. Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `tr2h : ∀ {a b b' : B.G Dp.D} (e : b = b') (w : B.P Dp.D a b), HEq (B.tr2 e w) w`. Introduce `a b b' e w`.

Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `tr1s : ∀ {a a' b : B.G Dp.D} (e : a = a') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b), B.tr1 e (B.smul l w) = B.smul l (B.tr1 e w)`. Introduce `a a' b e l w`. Substitute `e` using the available equality.

Both sides reduce to the same expression. Establish `tr2s : ∀ {a b b' : B.G Dp.D} (e : b = b') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b), B.tr2 e (B.smul l w) = B.smul l (B.tr2 e w)`. Introduce `a b b' e l w`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Establish `hπσ : B.map Dp.π (B.map Dp.σ y) = y`. Rewrite using `[← B.map_comp]`. Establish `: Dp.π.comp Dp.σ = LHom.id R` using `Subtype.ext (AlgHom.ext fun r => Dp.sect r)`. Rewrite using `[this, B.map_id]`. Establish `hker : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, B.map Dp.π (B.tg Dp.π Dp.sqZero Y') = 0` using `fun Y' => (B.tg_ker _ _ _).mpr ⟨Y', rfl⟩`.

Establish `hNx : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, N • B.tg Dp.π Dp.sqZero Y' = 0`. Introduce `Y'`. Rewrite using `[← map_nsmul, B.nsmul_tensor_eq_zero (Dp.natCast_D hN) _ Y', map_zero]`. Establish `hNy : N • B.map Dp.σ y = 0`. Take `⟨z, ⟨_, hy', _⟩, _⟩` from `hh 0`.

Conclude with `hy'`. Establish `hEmem : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y' ∈ RingHom.ker Dp.π.1` using `fun Y' => evalT_mem _ (RingHom.ker Dp.π.1) Y'`. Establish `claim : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, B.HtC Dp N y (B.tg Dp.π Dp.sqZero Y') (evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y')`. Introduce `Y'`. Proceed by induction on `Y' using TensorProduct.induction_on with`.

Consider the case `zero`. Use `B.HtC_congr Dp (map_zero _).symm (evalT_zero _ _).symm ?_` and prove the remaining obligations. Use `⟨B.zero1 (B.map Dp.σ y), ?_, B.nsmul1_zero1 _ N, 1, by simp, ?_⟩` and prove the remaining obligations. Use `(B.zeroFst_nat Dp.π _).trans ?_` and prove the remaining obligations. Rewrite using `[hπσ]`.

Use `(B.nsmul2_zero1 _ N).trans ?_` and prove the remaining obligations. Rewrite using `[hNy, B.zeroFst_zero, B.one_smul]`. Consider the case `tmul g k`. Take `⟨z, ⟨hx1, hy1, u, l₁, l₂, e1, e2, hz⟩, hzv⟩` from `hh g`. Take `⟨u', hu'⟩` from `B.exists_lift_red Dp (hker _) hπσ (B.zero1 y)`.

Establish `hB1` using `(hB2 R Dp N hN).1 y g u' hu'`. Take `⟨m, hm⟩` from `B.exists_smul u u'`. Establish `e1' : B.tr1 hx1 (B.nsmul1 u' N) = B.zero1 (B.map Dp.σ y)` using `eq_of_heq ((tr1h hx1 _).trans hB1)`. Rewrite `e1'` using `[← hm, B.nsmul1_smul, tr1s, e1, ← B.mul_smul]`. Establish `hml : m ^ N * l₁ = 1` using `B.smul_eq_self e1'`.

Establish `hl1 : l₁ = (m ^ N)⁻¹` using `eq_inv_of_mul_eq_one_right hml`. Establish `e2' : B.tr2 hy1 (B.nsmul2 u' N) = B.smul (m ^ N * l₂) (B.zero2 _)`. Rewrite using `[← hm, B.nsmul2_smul, tr2s, e2, ← B.mul_smul]`. Establish `hc0 : m ^ N * l₂ = z⁻¹`. Rewrite using `[hz, hl1, div_eq_mul_inv, mul_inv, inv_inv, inv_inv]`.

Establish `hzinv : ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u)) = 1 - Dp.σ.1 (h g) * Dp.η`. Establish `hmul : (z : (Dp.D : Type u)) * (1 - Dp.σ.1 (h g) * Dp.η) = 1`. Rewrite using `[hzv]`. Take the linear combination `-(Dp.σ.1 (h g) * Dp.σ.1 (h g)) * Dp.η_sq`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmul, mul_one]`. Use `_ = 1 - Dp.σ.1 (h g) * Dp.η := by rw [← mul_assoc, Units.inv_mul, one_mul]`. Use `set r : (R : Type u) := Dp.κ (k : (Dp.D : Type u)) with hr`. Establish `hk0 : Dp.π.1 (k : (Dp.D : Type u)) = 0` using `k.2`. Establish `hk : (k : (Dp.D : Type u)) = Dp.σ.1 r * Dp.η`.

Use `Dp.decomp (k : (Dp.D : Type u))` as an intermediate fact. Rewrite `this` using `[hk0, map_zero, zero_add]`. Conclude with `this`. Use `set f := Dp.fr r with hfdef`. Establish `hfσ : ∀ s : (R : Type u), f.1 (Dp.σ.1 s) = Dp.σ.1 s`.

Introduce `s`. Use `congrArg (fun φ : LHom R Dp.D => φ.1 s) (Dp.fr_comp_σ r)` as an intermediate fact. Conclude with `this`. Establish `hfk : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dp.π.ker`. Introduce `a ha`.

Establish `h1` using `congrArg (fun φ : LHom Dp.D R => φ.1 a) (Dp.π_comp_fr r)`. Use `show Dp.π.1 (f.1 a) = 0`. Establish `h2 : Dp.π.1 a = 0` using `ha`. Rewrite using `[← h2]`. Conclude with `h1`.

Establish `hfy : B.map f (B.map Dp.σ y) = B.map Dp.σ y`. Rewrite using `[← B.map_comp, Dp.fr_comp_σ]`. Establish `hfx : B.map f (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = B.tg Dp.π Dp.sqZero (g ⊗ₜ k)`. Rewrite using `[← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero f hfk, LinearMap.lTensor_tmul]`. Use `congr 2`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show f.1 Dp.η = (k : (Dp.D : Type u))`. Rewrite using `[hk, Dp.fr_η]`. Establish `hxk : B.map Dp.π (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = 0` using `hker _`. Use `⟨B.tr2 hfy (B.tr1 hfx (B.pmap f u')), ?_, ?_, Units.map (f.1 : (Dp.D : Type u) →* (Dp.D : Type u)) z⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : HEq (B.pmap Dp.π (B.tr2 hfy (B.tr1 hfx (B.pmap f u')))) (B.pmap Dp.π (B.pmap f u'))` using `pmap_heq Dp.π hfx.symm hfy.symm ((tr2h hfy _).trans (tr1h hfx _))`. Use `h1.trans ((B.pmap_comp f Dp.π u').symm.trans ?_)` and prove the remaining obligations. Conclude with `(B.pmap_congr_hom (Dp.π_comp_fr r) u').trans hu'`. Establish `h1 : HEq (B.nsmul1 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul1 (B.pmap f u') N)` using `B.nsmul1_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))`. Use `h1.trans ((B.pmap_nsmul1 f u' N).symm.trans ?_)` and prove the remaining obligations.

Use `(pmap_heq f hx1 rfl hB1).trans ((B.zeroFst_nat f _).trans ?_)` and prove the remaining obligations. Rewrite using `[hfy]`. Rewrite using `[Units.coe_map, MonoidHom.coe_coe, hzinv, evalT_tmul, map_sub, map_one, map_mul, hfσ, Dp.fr_η, hk]`. Apply the tactic sequence `try simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]`. Apply the tactic sequence `try ring`.

Establish `h1 : HEq (B.nsmul2 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul2 (B.pmap f u') N)` using `B.nsmul2_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))`. Use `h1.trans ((B.pmap_nsmul2 f u' N).symm.trans ?_)` and prove the remaining obligations. Establish `h2 : HEq (B.nsmul2 u' N) (B.smul z⁻¹ (B.zero2 (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk))))`. Rewrite using `[← hc0, ← e2']`. Conclude with `(tr2h hy1 _).symm`.

Use `(pmap_heq f rfl hy1 h2).trans ?_` and prove the remaining obligations. Rewrite using `[B.pmap_smul]`. Use `B.smul_hcongr hfx (map_zero _) _ ((B.zeroSnd_nat f _).trans ?_)` and prove the remaining obligations. Rewrite using `[hfx]`. Consider the case `add Y₁ Y₂ ih₁ ih₂`.

Use `B.HtC_congr Dp (map_add _ _ _).symm (evalT_add _ _ _ _).symm ?_` and prove the remaining obligations. Take `⟨v₁, r₁, n₁, c₁, hc₁, m₁⟩` from `ih₁`. Take `⟨v₂, r₂, n₂, c₂, hc₂, m₂⟩` from `ih₂`. Use `⟨B.add1 v₁ v₂, ?_, ?_, c₁ * c₂, ?_, ?_⟩` and prove the remaining obligations. Use `(B.addFst_nat Dp.π v₁ v₂).trans ?_` and prove the remaining obligations.

Use `(B.addFst_hcongr (hker Y₁) (hker Y₂) hπσ r₁ r₂).trans ?_` and prove the remaining obligations. Conclude with `B.zeroFst_add (B.zero1 y)`. Establish `hS : N • (B.S1mk (B.add1 v₁ v₂)) = 0`. Establish `e : B.S1mk (B.add1 v₁ v₂) = B.S1mk v₁ + B.S1mk v₂` using `rfl`. Establish `z1 : N • B.S1mk v₁ = 0`.

Rewrite using `[B.fibreFst_nsmul_mk]`. Conclude with `Sigma.ext (hNx Y₁) n₁`. Establish `z2 : N • B.S1mk v₂ = 0`. Rewrite using `[B.fibreFst_nsmul_mk]`. Conclude with `Sigma.ext (hNx Y₂) n₂`.

Rewrite using `[e, nsmul_add, z1, z2, add_zero]`. Rewrite `hS` using `[B.fibreFst_nsmul_mk]`. Conclude with `(Sigma.ext_iff.mp hS).2`. Take `⟨a₁, ha₁⟩` from `Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₁))`. Take `⟨a₂, ha₂⟩` from `Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₂))`.

Rewrite using `[Units.val_mul, hc₁, hc₂, ← ha₁, ← ha₂]`. Take the linear combination `(a₁ * a₂) * Dp.η_sq`. Rewrite using `[B.nsmulSnd_addFst]`. Use `(B.addFst_hcongr rfl rfl hNy m₁ m₂).trans ?_` and prove the remaining obligations. Rewrite using `[B.addFst_smul, B.zeroSnd_addFst]`.

Take `⟨v, hvr, hv1, c, hc, hv2⟩` from `claim Y`. Take `⟨s1, s2⟩` from `B.nsmul_of_same_red Dp hN (B.zero1 y) w₀ v hu hvr`. Use `⟨?_, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[s1]`. Conclude with `hv1`.

Rewrite using `[s2]`. Conclude with `hv2`.
-/
theorem ht_gen (hB2 : HighestWeightVectorUniformBounds B) (N : ℕ) (hN : (N : (R : Type u)) = 0) (y : B.G R)
    (h : B.gg →ₗ[R₀] R) (hh : B.IsHeight Dp N y h) (Y : B.gg ⊗[R₀] Dp.π.ker)
    (w₀ : B.P Dp.D (B.tg Dp.π Dp.sqZero Y) (B.map Dp.σ y))
    (hu : HEq (B.pmap Dp.π w₀) (B.zero1 y)) :
    HEq (B.nsmul1 w₀ N) (B.zero1 (B.map Dp.σ y)) ∧
    ∃ c : (Dp.D : Type u)ˣ,
      (c : (Dp.D : Type u)) = 1 - evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y ∧
      HEq (B.nsmul2 w₀ N) (B.smul c (B.zero2 (B.tg Dp.π Dp.sqZero Y))) := by

  have pmap_heq : ∀ {S : LAlg R₀} (f : LHom Dp.D S) {a a' b b' : B.G Dp.D} (ha : a = a') (hb : b = b')
      {w : B.P Dp.D a b} {w' : B.P Dp.D a' b'}, HEq w w' → HEq (B.pmap f w) (B.pmap f w') := by
    intro S f a a' b b' ha hb w w' hw
    subst ha hb
    rw [eq_of_heq hw]
  have tr1h : ∀ {a a' b : B.G Dp.D} (e : a = a') (w : B.P Dp.D a b), HEq (B.tr1 e w) w := by
    intro a a' b e w
    subst e
    rfl
  have tr2h : ∀ {a b b' : B.G Dp.D} (e : b = b') (w : B.P Dp.D a b), HEq (B.tr2 e w) w := by
    intro a b b' e w
    subst e
    rfl
  have tr1s : ∀ {a a' b : B.G Dp.D} (e : a = a') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b),
      B.tr1 e (B.smul l w) = B.smul l (B.tr1 e w) := by
    intro a a' b e l w
    subst e
    rfl
  have tr2s : ∀ {a b b' : B.G Dp.D} (e : b = b') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b),
      B.tr2 e (B.smul l w) = B.smul l (B.tr2 e w) := by
    intro a b b' e l w
    subst e
    rfl
  have hπσ : B.map Dp.π (B.map Dp.σ y) = y := by
    rw [← B.map_comp]
    have : Dp.π.comp Dp.σ = LHom.id R := Subtype.ext (AlgHom.ext fun r => Dp.sect r)
    rw [this, B.map_id]
  have hker : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, B.map Dp.π (B.tg Dp.π Dp.sqZero Y') = 0 :=
    fun Y' => (B.tg_ker _ _ _).mpr ⟨Y', rfl⟩
  have hNx : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, N • B.tg Dp.π Dp.sqZero Y' = 0 := by
    intro Y'
    rw [← map_nsmul, B.nsmul_tensor_eq_zero (Dp.natCast_D hN) _ Y', map_zero]
  have hNy : N • B.map Dp.σ y = 0 := by
    obtain ⟨z, ⟨_, hy', _⟩, _⟩ := hh 0
    exact hy'
  have hEmem : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker,
      evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y' ∈ RingHom.ker Dp.π.1 :=
    fun Y' => evalT_mem _ (RingHom.ker Dp.π.1) Y'

  have claim : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker,
      B.HtC Dp N y (B.tg Dp.π Dp.sqZero Y') (evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y') := by
    intro Y'
    induction Y' using TensorProduct.induction_on with
    | zero =>
      refine B.HtC_congr Dp (map_zero _).symm (evalT_zero _ _).symm ?_
      refine ⟨B.zero1 (B.map Dp.σ y), ?_, B.nsmul1_zero1 _ N, 1, by simp, ?_⟩
      · refine (B.zeroFst_nat Dp.π _).trans ?_
        rw [hπσ]
      · refine (B.nsmul2_zero1 _ N).trans ?_
        rw [hNy, B.zeroFst_zero, B.one_smul]
    | tmul g k =>
      obtain ⟨z, ⟨hx1, hy1, u, l₁, l₂, e1, e2, hz⟩, hzv⟩ := hh g
      obtain ⟨u', hu'⟩ := B.exists_lift_red Dp (hker _) hπσ (B.zero1 y)
      have hB1 := (hB2 R Dp N hN).1 y g u' hu'
      obtain ⟨m, hm⟩ := B.exists_smul u u'
      have e1' : B.tr1 hx1 (B.nsmul1 u' N) = B.zero1 (B.map Dp.σ y) :=
        eq_of_heq ((tr1h hx1 _).trans hB1)
      rw [← hm, B.nsmul1_smul, tr1s, e1, ← B.mul_smul] at e1'
      have hml : m ^ N * l₁ = 1 := B.smul_eq_self e1'
      have hl1 : l₁ = (m ^ N)⁻¹ := eq_inv_of_mul_eq_one_right hml
      have e2' : B.tr2 hy1 (B.nsmul2 u' N) = B.smul (m ^ N * l₂) (B.zero2 _) := by
        rw [← hm, B.nsmul2_smul, tr2s, e2, ← B.mul_smul]
      have hc0 : m ^ N * l₂ = z⁻¹ := by
        rw [hz, hl1, div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
      have hzinv : ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u)) = 1 - Dp.σ.1 (h g) * Dp.η := by
        have hmul : (z : (Dp.D : Type u)) * (1 - Dp.σ.1 (h g) * Dp.η) = 1 := by
          rw [hzv]
          linear_combination -(Dp.σ.1 (h g) * Dp.σ.1 (h g)) * Dp.η_sq
        calc ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u))
            = ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u)) * ((z : (Dp.D : Type u)) * (1 - Dp.σ.1 (h g) * Dp.η)) := by
              rw [hmul, mul_one]
          _ = 1 - Dp.σ.1 (h g) * Dp.η := by rw [← mul_assoc, Units.inv_mul, one_mul]

      set r : (R : Type u) := Dp.κ (k : (Dp.D : Type u)) with hr
      have hk0 : Dp.π.1 (k : (Dp.D : Type u)) = 0 := k.2
      have hk : (k : (Dp.D : Type u)) = Dp.σ.1 r * Dp.η := by
        have := Dp.decomp (k : (Dp.D : Type u))
        rw [hk0, map_zero, zero_add] at this
        exact this
      set f := Dp.fr r with hfdef
      have hfσ : ∀ s : (R : Type u), f.1 (Dp.σ.1 s) = Dp.σ.1 s := by
        intro s
        have := congrArg (fun φ : LHom R Dp.D => φ.1 s) (Dp.fr_comp_σ r)
        exact this
      have hfk : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dp.π.ker := by
        intro a ha
        have h1 := congrArg (fun φ : LHom Dp.D R => φ.1 a) (Dp.π_comp_fr r)
        show Dp.π.1 (f.1 a) = 0
        have h2 : Dp.π.1 a = 0 := ha
        rw [← h2]
        exact h1
      have hfy : B.map f (B.map Dp.σ y) = B.map Dp.σ y := by
        rw [← B.map_comp, Dp.fr_comp_σ]
      have hfx : B.map f (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = B.tg Dp.π Dp.sqZero (g ⊗ₜ k) := by
        rw [← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero f hfk, LinearMap.lTensor_tmul]
        congr 2
        apply Subtype.ext
        show f.1 Dp.η = (k : (Dp.D : Type u))
        rw [hk, Dp.fr_η]
      have hxk : B.map Dp.π (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = 0 := hker _
      refine ⟨B.tr2 hfy (B.tr1 hfx (B.pmap f u')), ?_, ?_, Units.map (f.1 : (Dp.D : Type u) →* (Dp.D : Type u)) z⁻¹, ?_, ?_⟩
      ·
        have h1 : HEq (B.pmap Dp.π (B.tr2 hfy (B.tr1 hfx (B.pmap f u')))) (B.pmap Dp.π (B.pmap f u')) :=
          pmap_heq Dp.π hfx.symm hfy.symm ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_comp f Dp.π u').symm.trans ?_)
        exact (B.pmap_congr_hom (Dp.π_comp_fr r) u').trans hu'
      ·
        have h1 : HEq (B.nsmul1 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul1 (B.pmap f u') N) :=
          B.nsmul1_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_nsmul1 f u' N).symm.trans ?_)
        refine (pmap_heq f hx1 rfl hB1).trans ((B.zeroFst_nat f _).trans ?_)
        rw [hfy]
      ·
        rw [Units.coe_map, MonoidHom.coe_coe, hzinv, evalT_tmul, map_sub, map_one, map_mul, hfσ, Dp.fr_η, hk]
        try simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
        try ring
      ·
        have h1 : HEq (B.nsmul2 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul2 (B.pmap f u') N) :=
          B.nsmul2_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_nsmul2 f u' N).symm.trans ?_)
        have h2 : HEq (B.nsmul2 u' N) (B.smul z⁻¹ (B.zero2 (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)))) := by
          rw [← hc0, ← e2']
          exact (tr2h hy1 _).symm
        refine (pmap_heq f rfl hy1 h2).trans ?_
        rw [B.pmap_smul]
        refine B.smul_hcongr hfx (map_zero _) _ ((B.zeroSnd_nat f _).trans ?_)
        rw [hfx]
    | add Y₁ Y₂ ih₁ ih₂ =>
      refine B.HtC_congr Dp (map_add _ _ _).symm (evalT_add _ _ _ _).symm ?_
      obtain ⟨v₁, r₁, n₁, c₁, hc₁, m₁⟩ := ih₁
      obtain ⟨v₂, r₂, n₂, c₂, hc₂, m₂⟩ := ih₂
      refine ⟨B.add1 v₁ v₂, ?_, ?_, c₁ * c₂, ?_, ?_⟩
      · refine (B.addFst_nat Dp.π v₁ v₂).trans ?_
        refine (B.addFst_hcongr (hker Y₁) (hker Y₂) hπσ r₁ r₂).trans ?_
        exact B.zeroFst_add (B.zero1 y)
      · have hS : N • (B.S1mk (B.add1 v₁ v₂)) = 0 := by
          have e : B.S1mk (B.add1 v₁ v₂) = B.S1mk v₁ + B.S1mk v₂ := rfl
          have z1 : N • B.S1mk v₁ = 0 := by
            rw [B.fibreFst_nsmul_mk]
            exact Sigma.ext (hNx Y₁) n₁
          have z2 : N • B.S1mk v₂ = 0 := by
            rw [B.fibreFst_nsmul_mk]
            exact Sigma.ext (hNx Y₂) n₂
          rw [e, nsmul_add, z1, z2, add_zero]
        rw [B.fibreFst_nsmul_mk] at hS
        exact (Sigma.ext_iff.mp hS).2
      · obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₁))
        obtain ⟨a₂, ha₂⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₂))
        rw [Units.val_mul, hc₁, hc₂, ← ha₁, ← ha₂]
        linear_combination (a₁ * a₂) * Dp.η_sq
      · rw [B.nsmulSnd_addFst]
        refine (B.addFst_hcongr rfl rfl hNy m₁ m₂).trans ?_
        rw [B.addFst_smul, B.zeroSnd_addFst]
  obtain ⟨v, hvr, hv1, c, hc, hv2⟩ := claim Y
  obtain ⟨s1, s2⟩ := B.nsmul_of_same_red Dp hN (B.zero1 y) w₀ v hu hvr
  refine ⟨?_, c, hc, ?_⟩
  · rw [s1]
    exact hv1
  · rw [s2]
    exact hv2

end BX

end ReciprocityTheory.PGsh
