import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc
open scoped TensorProduct

/- English proof (translation)
Use `choose i a k e using fun g => hx (l g)`. Use `⟨Finset.univ.image fun j : Fin n => Function.invFun i j, fun g => ?_⟩` and prove the remaining obligations. Use `set s := Function.invFun i (i g) with hs`. Establish `hi : i s = i g` using `Function.invFun_eq ⟨g, rfl⟩`. Take `⟨γ, hγ⟩` from `hA ((a g : H) * (a s : H)⁻¹) (A.mul_mem (a g).2 (A.inv_mem (a s).2))`.

Use `⟨γ, s, Finset.mem_image_of_mem _ (Finset.mem_univ _), (ι γ * s)⁻¹ * g, ⟨(k s : H)⁻¹ * k g, K.mul_mem (K.inv_mem (k s).2) (k g).2, fun v => ?_⟩, by group⟩` and prove the remaining obligations. Establish `h1 : l g = ((a g : H) * (a s : H)⁻¹) * l s * ((k s : H)⁻¹ * k g)`. Rewrite using `[e g, e s, hi]`. Use `group`. Establish `h2 : m v g = m v (ι γ * s) * φ v ((k s : H)⁻¹ * k g)`.

Rewrite using `[← hl g v, h1, map_mul, map_mul, ← hγ, hl, map_mul (m v)]`. Rewrite using `[map_mul, h2, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]`.
-/
private theorem cover_abs {Γ G H I : Type} [Group Γ] [Group G] [Group H] {M : I → Type} [∀ v, Monoid (M v)]
    (ι : Γ →* G) (A K : Subgroup H) (l : G → H) (φ : ∀ v, H →* M v) (m : ∀ v, G →* M v) (hl : ∀ g v, φ v (l g) = m v g)
    (hA : ∀ a ∈ A, ∃ γ, ∀ v, m v (ι γ) = φ v a) {n : ℕ} (x : Fin n → H)
    (hx : ∀ h, ∃ i, ∃ a : A, ∃ k : K, h = (a : H) * x i * k) :
    ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u : G, (∃ k ∈ K, ∀ v, m v u = φ v k) ∧ g = ι γ * s * u := by
  classical
  choose i a k e using fun g => hx (l g)
  refine ⟨Finset.univ.image fun j : Fin n => Function.invFun i j, fun g => ?_⟩
  set s := Function.invFun i (i g) with hs
  have hi : i s = i g := Function.invFun_eq ⟨g, rfl⟩
  obtain ⟨γ, hγ⟩ := hA ((a g : H) * (a s : H)⁻¹) (A.mul_mem (a g).2 (A.inv_mem (a s).2))
  refine ⟨γ, s, Finset.mem_image_of_mem _ (Finset.mem_univ _), (ι γ * s)⁻¹ * g,
    ⟨(k s : H)⁻¹ * k g, K.mul_mem (K.inv_mem (k s).2) (k g).2, fun v => ?_⟩, by group⟩
  have h1 : l g = ((a g : H) * (a s : H)⁻¹) * l s * ((k s : H)⁻¹ * k g) := by
    rw [e g, e s, hi]; group
  have h2 : m v g = m v (ι γ * s) * φ v ((k s : H)⁻¹ * k g) := by
    rw [← hl g v, h1, map_mul, map_mul, ← hγ, hl, map_mul (m v)]
  rw [map_mul, h2, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private def qm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a : R} {b : S} (h : f a = b) : Lsq R a →+* Lsq S b where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp [h]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [qm]`.
-/
private theorem qm_star {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a : R} {b : S} (h : f a = b) (x : Lsq R a) :
    qm f h (star x) = star (qm f h x) := by
  ext <;> simp [qm]

section Ten

variable {F : Type} [Field F] (Δ : F) (R : Type) [CommRing R] [Algebra F R]

private def rho : Lsq R (algebraMap F R Δ) →+* R ⊗[F] Lsq F Δ where
  toFun x := x.re ⊗ₜ[F] 1 + x.im ⊗ₜ[F] QuadraticAlgebra.omega
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.TensorProduct.one_def]
  map_mul' x y := by
    have h : (QuadraticAlgebra.omega : Lsq F Δ) * QuadraticAlgebra.omega = Δ • 1 := by
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
      TensorProduct.add_tmul, h, mul_one, one_mul, zero_mul, TensorProduct.zero_tmul, add_zero, ← TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, mul_assoc]
    abel
  map_zero' := by simp
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, TensorProduct.add_tmul]; abel

private def psi : R ⊗[F] Lsq F Δ →+* Lsq R (algebraMap F R Δ) :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom F R (Lsq R (algebraMap F R Δ)))
    { qm (algebraMap F R) rfl with
      commutes' := fun r => by ext <;> simp [qm, QuadraticAlgebra.algebraMap_eq, IsScalarTower.algebraMap_apply F R (Lsq R (algebraMap F R Δ))] }
    fun _ _ => Commute.all _ _).toRingHom

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
private theorem psi_tmul (a : R) (x : Lsq F Δ) : psi Δ R (a ⊗ₜ x) = a • qm (algebraMap F R) rfl x := by
  rw [Algebra.smul_def]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `psi Δ R (_ + _) = _`. Rewrite using `[map_add, psi_tmul, psi_tmul]`. Apply the tactic sequence `ext <;> simp [qm, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`.
-/
private theorem psi_rho (x : Lsq R (algebraMap F R Δ)) : psi Δ R (rho Δ R x) = x := by
  change psi Δ R (_ + _) = _
  rw [map_add, psi_tmul, psi_tmul]
  ext <;> simp [qm, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private def sg : Lsq F Δ →ₐ[F] Lsq F Δ :=
  { starRingEnd (Lsq F Δ) with commutes' := fun r => by ext <;> simp [QuadraticAlgebra.algebraMap_eq, starRingEnd_apply] }

/- English proof (translation)
Establish `h : sg Δ QuadraticAlgebra.omega = -QuadraticAlgebra.omega`. Express the relevant statement in the definitionally equal form `star _ = _`. Apply the tactic sequence `ext <;> simp`. Express the relevant statement in the definitionally equal form `_ + _ = Algebra.TensorProduct.map (AlgHom.id F R) (sg Δ) (_ + _)`. Simplify using `[h, TensorProduct.neg_tmul, TensorProduct.tmul_neg]`.
-/
private theorem rho_star (x : Lsq R (algebraMap F R Δ)) :
    rho Δ R (star x) = Algebra.TensorProduct.map (AlgHom.id F R) (sg Δ) (rho Δ R x) := by
  have h : sg Δ QuadraticAlgebra.omega = -QuadraticAlgebra.omega := by
    change star _ = _
    ext <;> simp
  change _ + _ = Algebra.TensorProduct.map (AlgHom.id F R) (sg Δ) (_ + _)
  simp [h, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

end Ten

/- English proof (translation)
The claim follows from `h.map ((sg Δ).restrictScalars O)`.
-/
private theorem int_star {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {x : Lsq K Δ} (h : IsIntegral O x) :
    IsIntegral O (star x) :=
  h.map ((sg Δ).restrictScalars O)

/- English proof (translation)
Establish `hi : Function.Injective (IsScalarTower.toAlgHom O K (Lsq K Δ))` using `fun a b e => by`. Simplify `congrArg QuadraticAlgebra.re e` using `[QuadraticAlgebra.algebraMap_eq]`. Establish `h1 : ∀ y : Lsq K Δ, IsIntegral O y → IsIntegral O (2 * y.re)` using `fun y hy => by`. Rewrite using `[← isIntegral_algHom_iff _ hi]`. Use `hy.add (int_star hy) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq, two_mul]`. Establish `hω : IsIntegral O (QuadraticAlgebra.omega : Lsq K Δ)`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Use `hΔ.map (IsScalarTower.toAlgHom O K (Lsq K Δ)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq, pow_two]`.

Use `⟨h1 x h, ?_⟩` and prove the remaining obligations. Use `h1 _ (hω.mul h) using 1` and compare the differences between its conclusion and the goal. Simplify using `[mul_assoc]`.
-/
private theorem int_coord {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} (hΔ : IsIntegral O Δ) {x : Lsq K Δ}
    (h : IsIntegral O x) : IsIntegral O (2 * x.re) ∧ IsIntegral O (2 * Δ * x.im) := by
  have hi : Function.Injective (IsScalarTower.toAlgHom O K (Lsq K Δ)) := fun a b e => by
    simpa [QuadraticAlgebra.algebraMap_eq] using congrArg QuadraticAlgebra.re e
  have h1 : ∀ y : Lsq K Δ, IsIntegral O y → IsIntegral O (2 * y.re) := fun y hy => by
    rw [← isIntegral_algHom_iff _ hi]
    convert hy.add (int_star hy) using 1
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, two_mul]
  have hω : IsIntegral O (QuadraticAlgebra.omega : Lsq K Δ) := by
    refine IsIntegral.of_pow two_pos ?_
    convert hΔ.map (IsScalarTower.toAlgHom O K (Lsq K Δ)) using 1
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, pow_two]
  refine ⟨h1 x h, ?_⟩
  convert h1 _ (hω.mul h) using 1
  simp [mul_assoc]

section Adel

open PI.UJClassFin

variable {F : Type} [Field F] [NumberField F] (Δ : F)

private def evf (v : Pl F) : Af F ⊗[F] Lsq F Δ →+* Lsq (Kv v) (cv v Δ) :=
  (qm (evalV F v).toRingHom ((evalV F v).commutes Δ)).comp (psi Δ (Af F))

private def eva (v : Pl F) : Lsq (AF F) (algebraMap F (AF F) Δ) →+* Lsq (Kv v) (cv v Δ) :=
  qm ((evalV F v).comp (sndA F)).toRingHom (((evalV F v).comp (sndA F)).commutes Δ)

private def ev (v : Pl F) : AF F ⊗[F] Lsq F Δ →+* Lsq (Kv v) (cv v Δ) := (eva Δ v).comp (psi Δ (AF F))

/- English proof (translation)
Rewrite using `[evf, RingHom.comp_apply, psi_tmul]`. Apply the tactic sequence `ext <;> simp [qm, lmap]`.
-/
private theorem evf_tmul (v : Pl F) (a : Af F) (x : Lsq F Δ) : evf Δ v (a ⊗ₜ x) = evalV F v a • lmap (cv v) Δ x := by
  rw [evf, RingHom.comp_apply, psi_tmul]
  ext <;> simp [qm, lmap]

/- English proof (translation)
Rewrite using `[ev, RingHom.comp_apply, psi_tmul]`. Apply the tactic sequence `ext <;> simp [eva, qm, lmap]`.
-/
private theorem ev_tmul (v : Pl F) (a : AF F) (x : Lsq F Δ) : ev Δ v (a ⊗ₜ x) = evalV F v (sndA F a) • lmap (cv v) Δ x := by
  rw [ev, RingHom.comp_apply, psi_tmul]
  ext <;> simp [eva, qm, lmap]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [ev_tmul, Algebra.TensorProduct.map_tmul, evf_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem ev_eq (v : Pl F) (z : AF F ⊗[F] Lsq F Δ) :
    ev Δ v z = evf Δ v (Algebra.TensorProduct.map (sndA F) (AlgHom.id F (Lsq F Δ)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [ev_tmul, Algebra.TensorProduct.map_tmul, evf_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
The claim follows from `(algebraMap F (Af F) x).2`.
-/
private theorem ae_int (x : F) : ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

/- English proof (translation)
Take `⟨z, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := Ov v) (K := Kv v)).1 h`. Conclude with `z.2`.
-/
private theorem mem_of_int {v : Pl F} {y : Kv v} (h : IsIntegral (Ov v) y) : y ∈ v.adicCompletionIntegers F := by
  obtain ⟨z, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Ov v) (K := Kv v)).1 h
  exact z.2

/- English proof (translation)
Establish `h : ∀ᶠ v : Pl F in Filter.cofinite, (x v).re ∈ v.adicCompletionIntegers F ∧ (x v).im ∈ v.adicCompletionIntegers F` using `by filter_upwards [hx, ae_int Δ, ae_int (2 : F)⁻¹, ae_int (2 * Δ)⁻¹] with v h1 h2 h3 h4`. Take `⟨ha, hb⟩` from `int_coord (isIntegral_algebraMap (x := (⟨_, h2⟩ : Ov v))) h1`. Prove the components needed by the constructor for the conclusion. Use `mul_mem h3 (mem_of_int ha) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← mul_assoc, ← map_ofNat (cv v) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]`.

Use `mul_mem h4 (mem_of_int hb) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = _ * (2 * cv v Δ * _)`. Rewrite using `[← mul_assoc, ← map_ofNat (cv v) 2, ← map_mul, ← map_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hΔ), map_one, one_mul]`. Conclude with `⟨⟨(c, ⟨fun v => (x v).re, h.mono fun _ h => h.1⟩), (0, ⟨fun v => (x v).im, h.mono fun _ h => h.2⟩)⟩, fun v => rfl, rfl, rfl⟩`.
-/
private theorem exists_entry (hΔ : Δ ≠ 0) (c : Ainf F) (x : ∀ v : Pl F, Lsq (Kv v) (cv v Δ))
    (hx : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (x v)) :
    ∃ z : Lsq (AF F) (algebraMap F (AF F) Δ), (∀ v, eva Δ v z = x v) ∧ z.re.1 = c ∧ z.im.1 = 0 := by
  have h : ∀ᶠ v : Pl F in Filter.cofinite, (x v).re ∈ v.adicCompletionIntegers F ∧ (x v).im ∈ v.adicCompletionIntegers F := by
    filter_upwards [hx, ae_int Δ, ae_int (2 : F)⁻¹, ae_int (2 * Δ)⁻¹] with v h1 h2 h3 h4
    obtain ⟨ha, hb⟩ := int_coord (isIntegral_algebraMap (x := (⟨_, h2⟩ : Ov v))) h1
    constructor
    · convert mul_mem h3 (mem_of_int ha) using 1
      rw [← mul_assoc, ← map_ofNat (cv v) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
    · convert mul_mem h4 (mem_of_int hb) using 1
      change _ = _ * (2 * cv v Δ * _)
      rw [← mul_assoc, ← map_ofNat (cv v) 2, ← map_mul, ← map_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hΔ), map_one, one_mul]
  exact ⟨⟨(c, ⟨fun v => (x v).re, h.mono fun _ h => h.1⟩), (0, ⟨fun v => (x v).im, h.mono fun _ h => h.2⟩)⟩,
    fun v => rfl, rfl, rfl⟩

/- English proof (translation)
Establish `hg : ∀ᶠ v : Pl F in Filter.cofinite, g.1 v ∈ KU (Ov v) (cv v Δ)` using `g.2`. Apply the tactic sequence `choose A h1 h2 h3 using fun i j : Fin 3 => exists_entry Δ hΔ ((1 : Matrix (Fin 3) (Fin 3) (Ainf F)) i j) (fun v => (g.1 v : Matrix (Fin 3) (Fin 3) _) i j) (hg.mono fun v h => (h i j).1)`. Establish `hv : ∀ v, (Matrix.of A).map (eva Δ v) = (g.1 v : Matrix (Fin 3) (Fin 3) _)` using `fun v => by ext1 i j; exact h1 i j v`. Use `⟨Matrix.of A, ?_, hv⟩` and prove the remaining obligations. Set `q : Lsq (AF F) (algebraMap F (AF F) Δ) →+* Lsq (Ainf F) (algebraMap F (AF F) Δ).1` to `qm (RingHom.fst (Ainf F) (Af F)) rfl`.

Establish `hq : (Matrix.of A).map q = 1` using `by ext1 i j`. Apply the tactic sequence `refine QuadraticAlgebra.ext ((h2 i j).trans ?_) ((h3 i j).trans ?_) <;>`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Establish `a1 : (star (Matrix.of A) * Matrix.of A).map q = (1 : Matrix (Fin 3) (Fin 3) _).map q`. Rewrite using `[Matrix.map_mul, star_eq_conjTranspose, conjTranspose_map q (qm_star _ _), hq, Matrix.map_one _ (map_zero q) (map_one q)]`.

Simplify using the standard rewrite rules. Establish `a2 : ∀ v, (star (Matrix.of A) * Matrix.of A).map (eva Δ v) = (1 : Matrix (Fin 3) (Fin 3) _).map (eva Δ v)` using `fun v => by`. Rewrite using `[Matrix.map_mul, star_eq_conjTranspose, conjTranspose_map (eva Δ v) (qm_star _ _), hv, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `(g.1 v).2.1`. Use `ext1 i j`.

Establish `b1` using `congrFun (congrFun a1 i) j`. Establish `b2` using `fun v => congrFun (congrFun (a2 v) i) j`. Rewrite `b1` using `[Matrix.map_apply, Matrix.map_apply]`. Simplify using `only [Matrix.map_apply] at b2`. Use `QuadraticAlgebra.ext (Prod.ext (congrArg QuadraticAlgebra.re b1) ?_) (Prod.ext (congrArg QuadraticAlgebra.im b1) ?_)` and prove the remaining obligations.

Conclude with `FiniteAdeleRing.ext _ fun v => congrArg QuadraticAlgebra.re (b2 v)`. Conclude with `FiniteAdeleRing.ext _ fun v => congrArg QuadraticAlgebra.im (b2 v)`.
-/
private theorem exists_mat (hΔ : Δ ≠ 0) (g : GA Δ) :
    ∃ A : Matrix (Fin 3) (Fin 3) (Lsq (AF F) (algebraMap F (AF F) Δ)), star A * A = 1 ∧
      ∀ v, A.map (eva Δ v) = (g.1 v : Matrix (Fin 3) (Fin 3) _) := by
  have hg : ∀ᶠ v : Pl F in Filter.cofinite, g.1 v ∈ KU (Ov v) (cv v Δ) := g.2
  choose A h1 h2 h3 using fun i j : Fin 3 => exists_entry Δ hΔ ((1 : Matrix (Fin 3) (Fin 3) (Ainf F)) i j)
    (fun v => (g.1 v : Matrix (Fin 3) (Fin 3) _) i j) (hg.mono fun v h => (h i j).1)
  have hv : ∀ v, (Matrix.of A).map (eva Δ v) = (g.1 v : Matrix (Fin 3) (Fin 3) _) := fun v => by
    ext1 i j; exact h1 i j v
  refine ⟨Matrix.of A, ?_, hv⟩
  let q : Lsq (AF F) (algebraMap F (AF F) Δ) →+* Lsq (Ainf F) (algebraMap F (AF F) Δ).1 := qm (RingHom.fst (Ainf F) (Af F)) rfl
  have hq : (Matrix.of A).map q = 1 := by
    ext1 i j
    refine QuadraticAlgebra.ext ((h2 i j).trans ?_) ((h3 i j).trans ?_) <;>
    by_cases h : i = j <;> simp [Matrix.one_apply, h, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have a1 : (star (Matrix.of A) * Matrix.of A).map q = (1 : Matrix (Fin 3) (Fin 3) _).map q := by
    rw [Matrix.map_mul, star_eq_conjTranspose, conjTranspose_map q (qm_star _ _), hq, Matrix.map_one _ (map_zero q) (map_one q)]
    simp
  have a2 : ∀ v, (star (Matrix.of A) * Matrix.of A).map (eva Δ v) = (1 : Matrix (Fin 3) (Fin 3) _).map (eva Δ v) := fun v => by
    rw [Matrix.map_mul, star_eq_conjTranspose, conjTranspose_map (eva Δ v) (qm_star _ _), hv,
      Matrix.map_one _ (map_zero _) (map_one _)]
    exact (g.1 v).2.1
  ext1 i j
  have b1 := congrFun (congrFun a1 i) j
  have b2 := fun v => congrFun (congrFun (a2 v) i) j
  rw [Matrix.map_apply, Matrix.map_apply] at b1
  simp only [Matrix.map_apply] at b2
  refine QuadraticAlgebra.ext (Prod.ext (congrArg QuadraticAlgebra.re b1) ?_) (Prod.ext (congrArg QuadraticAlgebra.im b1) ?_)
  · exact FiniteAdeleRing.ext _ fun v => congrArg QuadraticAlgebra.re (b2 v)
  · exact FiniteAdeleRing.ext _ fun v => congrArg QuadraticAlgebra.im (b2 v)

end Adel

section Main

open PI.UJClassFin

variable {F : Type} [Field F] [NumberField F] (Δ : F) [Fact (∀ r : F, r ^ 2 ≠ Δ + 0 * r)]

private instance : NumberField (Lsq F Δ) := NumberField.of_module_finite F _

private abbrev HH : Type := HA (AF F) (sg Δ) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ))

private def phi (v : Pl F) : HH Δ →* Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ)) where
  toFun h := ((HA.mat (AF F) (sg Δ) 1 h : GL (Fin 3) _) : Matrix (Fin 3) (Fin 3) (AF F ⊗[F] Lsq F Δ)).map (ev Δ v)
  map_one' := by
    rw [HA_mat_one, Units.val_one]; exact Matrix.map_one _ (map_zero _) (map_one _)
  map_mul' a b := by
    rw [HA_mat_mul, Units.val_mul]; exact Matrix.map_mul

/- English proof (translation)
Take `⟨A, hA, hv⟩` from `exists_mat Δ hΔ g`. Establish `h1 : (star A).map (rho Δ (AF F)) * A.map (rho Δ (AF F)) = 1`. Rewrite using `[← Matrix.map_mul, hA]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Use `⟨(⟨⟨A.map (rho Δ (AF F)), _, mul_eq_one_comm.1 h1, h1⟩, ?_⟩ : HR (AF F) (sg Δ) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ))), fun v => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `cT _ (A.map (rho Δ (AF F))) * JR _ 1 * A.map (rho Δ (AF F)) = JR _ 1`. Establish `hJ : JR (AF F) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) = (1 : Matrix (Fin 3) (Fin 3) (AF F ⊗[F] Lsq F Δ))` using `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[hJ, Matrix.mul_one, ← h1]`. Use `congr 1`. Use `ext1 i j`.

Conclude with `(rho_star Δ (AF F) (A j i)).symm`. Rewrite using `[← hv v] ext1 i j`. Conclude with `congrArg (eva Δ v) (psi_rho Δ (AF F) (A i j))`.
-/
private theorem exists_lift (hΔ : Δ ≠ 0) (g : GA Δ) : ∃ h : HH Δ, ∀ v, phi Δ v h = (g.1 v : Matrix (Fin 3) (Fin 3) _) := by
  obtain ⟨A, hA, hv⟩ := exists_mat Δ hΔ g
  have h1 : (star A).map (rho Δ (AF F)) * A.map (rho Δ (AF F)) = 1 := by
    rw [← Matrix.map_mul, hA]; exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨(⟨⟨A.map (rho Δ (AF F)), _, mul_eq_one_comm.1 h1, h1⟩, ?_⟩ : HR (AF F) (sg Δ) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ))), fun v => ?_⟩
  · change cT _ (A.map (rho Δ (AF F))) * JR _ 1 * A.map (rho Δ (AF F)) = JR _ 1
    have hJ : JR (AF F) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) = (1 : Matrix (Fin 3) (Fin 3) (AF F ⊗[F] Lsq F Δ)) :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hJ, Matrix.mul_one, ← h1]
    congr 1
    ext1 i j
    exact (rho_star Δ (AF F) (A j i)).symm
  · rw [← hv v]
    ext1 i j
    exact congrArg (eva Δ v) (psi_rho Δ (AF F) (A i j))

/- English proof (translation)
Take `⟨x, hx, e⟩` from `Subgroup.mem_subgroupOf.1 ha`. Establish `h1 : star (x : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) * x = 1`. Establish `h : cT _ (x : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) * 1 * x = 1` using `hx`. Rewrite `h` using `[Matrix.mul_one]`. Conclude with `h`.

Use `⟨⟨x, h1, mul_eq_one_comm.1 h1⟩, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hι]`. Use `ext1 i j`. Establish `e' : (HA.mat (AF F) (sg Δ) 1 a : GL (Fin 3) _) = bc (inclR (AF F)) x` using `e.symm`. Express the relevant statement in the definitionally equal form `_ = ev Δ v (((HA.mat (AF F) (sg Δ) 1 a : GL (Fin 3) _) : Matrix (Fin 3) (Fin 3) (AF F ⊗[F] Lsq F Δ)) i j)`.

Rewrite using `[e']`. Express the relevant statement in the definitionally equal form `lmap (cv v) Δ (x.1 i j) = ev Δ v ((1 : AF F) ⊗ₜ x.1 i j)`. Rewrite using `[ev_tmul, map_one, map_one, one_smul]`.
-/
private theorem exists_rat (ι : U3 Δ →* GA Δ) (hι : IsIotaG ι) (a : HH Δ) (ha : a ∈ GamG (sg Δ) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ))) :
    ∃ γ, ∀ v, ((ι γ).1 v : Matrix (Fin 3) (Fin 3) _) = phi Δ v a := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_subgroupOf.1 ha
  have h1 : star (x : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) * x = 1 := by
    have h : cT _ (x : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) * 1 * x = 1 := hx
    rw [Matrix.mul_one] at h
    exact h
  refine ⟨⟨x, h1, mul_eq_one_comm.1 h1⟩, fun v => ?_⟩
  rw [hι]
  ext1 i j
  have e' : (HA.mat (AF F) (sg Δ) 1 a : GL (Fin 3) _) = bc (inclR (AF F)) x := e.symm
  change _ = ev Δ v (((HA.mat (AF F) (sg Δ) 1 a : GL (Fin 3) _) : Matrix (Fin 3) (Fin 3) (AF F ⊗[F] Lsq F Δ)) i j)
  rw [e']
  change lmap (cv v) Δ (x.1 i j) = ev Δ v ((1 : AF F) ⊗ₜ x.1 i j)
  rw [ev_tmul, map_one, map_one, one_smul]

/- English proof (translation)
Establish `h1 : ∀ y ∈ latHat F (Lsq F Δ) {x : Fin 3 → Lsq F Δ | ∀ i, IsIntegral ℤ (x i)}, IsIntegral (Ov v) (evf Δ v (y i))`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`.

Establish `: IsIntegral (Ov v) (lmap (cv v) Δ (x i))` using `(hx i).map_of_comp_eq (Int.castRingHom (Ov v)) (lmap (cv v) Δ) (RingHom.ext_int _ _)`. Rewrite using `[evf_tmul]`. Conclude with `this.smul (⟨_, ha v⟩ : Ov v)`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, map_add]`.

Conclude with `hx.add hy`. Consider the case `neg x _ hx => rw [Pi.neg_apply, map_neg]`. Conclude with `hx.neg`. Establish `h2 : (Pi.single j 1 : Fin 3 → Af F ⊗[F] Lsq F Δ) ∈ latHat F (Lsq F Δ) {x : Fin 3 → Lsq F Δ | ∀ i, IsIntegral ℤ (x i)}`. Use `AddSubgroup.subset_closure ⟨1, fun w => ?_, Pi.single j 1, fun i => ?_, funext fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one]`. Conclude with `one_mem _`. Apply the tactic sequence `by_cases h : i = j <;> simp [Pi.single_apply, h, isIntegral_one, isIntegral_zero]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Pi.single_apply, h, Algebra.TensorProduct.one_def]`. Establish `h3` using `h1 _ ((hk _).1 h2)`.

Rewrite `h3` using `[Matrix.mulVec_single_one]`. Express the relevant statement in the definitionally equal form `IsIntegral (Ov v) (ev Δ v _)`. Rewrite using `[ev_eq]`. Conclude with `h3`.
-/
private theorem int_of_stab (k : HH Δ)
    (hk : k ∈ SFin (sg Δ) (1 : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) {x : Fin 3 → Lsq F Δ | ∀ i, IsIntegral ℤ (x i)}) (v : Pl F) (i j : Fin 3) :
    IsIntegral (Ov v) (phi Δ v k i j) := by
  have h1 : ∀ y ∈ latHat F (Lsq F Δ) {x : Fin 3 → Lsq F Δ | ∀ i, IsIntegral ℤ (x i)}, IsIntegral (Ov v) (evf Δ v (y i)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have : IsIntegral (Ov v) (lmap (cv v) Δ (x i)) :=
        (hx i).map_of_comp_eq (Int.castRingHom (Ov v)) (lmap (cv v) Δ) (RingHom.ext_int _ _)
      rw [evf_tmul]
      exact this.smul (⟨_, ha v⟩ : Ov v)
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy => rw [Pi.add_apply, map_add]; exact hx.add hy
    | neg x _ hx => rw [Pi.neg_apply, map_neg]; exact hx.neg
  have h2 : (Pi.single j 1 : Fin 3 → Af F ⊗[F] Lsq F Δ) ∈ latHat F (Lsq F Δ) {x : Fin 3 → Lsq F Δ | ∀ i, IsIntegral ℤ (x i)} := by
    refine AddSubgroup.subset_closure ⟨1, fun w => ?_, Pi.single j 1, fun i => ?_, funext fun i => ?_⟩
    · rw [map_one]; exact one_mem _
    · by_cases h : i = j <;> simp [Pi.single_apply, h, isIntegral_one, isIntegral_zero]
    · by_cases h : i = j <;> simp [Pi.single_apply, h, Algebra.TensorProduct.one_def]
  have h3 := h1 _ ((hk _).1 h2)
  rw [Matrix.mulVec_single_one] at h3
  change IsIntegral (Ov v) (ev Δ v _)
  rw [ev_eq]
  exact h3

omit [NumberField F] in
/- English proof (translation)
Establish `hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F (Lsq F Δ)))` using `IsTotallyReal.complexEmbedding_isReal _`. Take `⟨f, h0⟩ : ∃ f : F →+* ℝ, ∀ x, τ (algebraMap F _ x) = f x` from `⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩`. Establish `h1 : τ QuadraticAlgebra.omega * τ QuadraticAlgebra.omega = f Δ`. Rewrite using `[← map_mul, ← h0]`. Use `congr 1`.

Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq]`. Establish `h2 : (τ QuadraticAlgebra.omega).re = 0`. Establish `hre` using `congrArg Complex.re h1`. Establish `him` using `congrArg Complex.im h1`. Use `hneg f` as an intermediate fact.

Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him`. Assume the negation of the conclusion as `hne`. Establish `: (τ QuadraticAlgebra.omega).im = 0`. Establish `: (τ QuadraticAlgebra.omega).re * (τ QuadraticAlgebra.omega).im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`.

Use polynomial arithmetic with `[mul_self_nonneg (τ QuadraticAlgebra.omega).re]`. Establish `e1 : a = algebraMap F _ a.re + algebraMap F _ a.im * QuadraticAlgebra.omega`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq]`. Establish `e2 : star a = algebraMap F _ a.re - algebraMap F _ a.im * QuadraticAlgebra.omega`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq]`.

Rewrite using `[e2]`. Use `conv_rhs => rw [e1]`. Simplify using `only [map_add, map_sub, map_mul, h0, Complex.conj_ofReal]`. Apply the tactic sequence `apply Complex.ext <;> simp [h2]`.
-/
private theorem emb_star [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (τ : Lsq F Δ →+* ℂ) (a : Lsq F Δ) :
    τ (star a) = starRingEnd ℂ (τ a) := by
  have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F (Lsq F Δ))) := IsTotallyReal.complexEmbedding_isReal _
  obtain ⟨f, h0⟩ : ∃ f : F →+* ℝ, ∀ x, τ (algebraMap F _ x) = f x := ⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩
  have h1 : τ QuadraticAlgebra.omega * τ QuadraticAlgebra.omega = f Δ := by
    rw [← map_mul, ← h0]
    congr 1
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have h2 : (τ QuadraticAlgebra.omega).re = 0 := by
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    have := hneg f
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    by_contra hne
    have : (τ QuadraticAlgebra.omega).im = 0 := by
      have : (τ QuadraticAlgebra.omega).re * (τ QuadraticAlgebra.omega).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    nlinarith [mul_self_nonneg (τ QuadraticAlgebra.omega).re]
  have e1 : a = algebraMap F _ a.re + algebraMap F _ a.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have e2 : star a = algebraMap F _ a.re - algebraMap F _ a.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  rw [e2]
  conv_rhs => rw [e1]
  simp only [map_add, map_sub, map_mul, h0, Complex.conj_ofReal]
  apply Complex.ext <;> simp [h2]

end Main

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h0` using `hneg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))`. Establish `hΔ : Δ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h0`.

Use `haveI : Fact (∀ r : F, r ^ 2 ≠ Δ + 0 * r) := ⟨fun r hr => by`. Rewrite `hr` using `[zero_mul, add_zero]`. Rewrite `h0` using `[← hr, map_pow]`. Conclude with `absurd (sq_nonneg _) (not_le.2 h0)⟩`. Take `⟨n, x, hx, -⟩` from `unitary_class_set_finite F (Lsq F Δ) (sg Δ) 3 1 {x | ∀ i, IsIntegral ℤ (x i)} (fun _ => rfl) (emb_star Δ hneg) (fun τ => ⟨(Equiv.sumEmpty _ _).symm, 1, by`.

Rewrite using `[Matrix.map_one _ (map_zero τ) (map_one τ), Units.val_one, PI.UJClassFin.cT_one]`. Use extensionality with `(i | i) (j | j)`. Simplify using `[PI.UJClassFin.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`.

Conclude with `i.elim0⟩)`. Use the proof step `⟨1, one_ne_zero, fun x hx i => by simpa using hx i⟩`. Apply the tactic sequence `⟨1, one_ne_zero, fun i e he j => by by_cases h : j = i <;> simp [Pi.single_apply, h, he, isIntegral_zero]⟩`. Use `choose l hl using exists_lift Δ hΔ`. Take `⟨S, hS⟩` from `cover_abs ι _ _ l (phi Δ) (fun v => (Matrix.unitaryGroup (Fin 3) (Lsq (Kv v) (cv v Δ))).subtype.comp ((rpg _ _).p v)) hl (exists_rat Δ ι hι) x hx`.

Use `⟨S, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, s, hs, u, ⟨k, hk, hu⟩, e⟩` from `hS g`. Use `⟨γ, s, hs, u, fun v i j => ?_, e⟩` and prove the remaining obligations. Establish `h : IsIntegral (Ov v) ((u.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) i j)`. Use `int_of_stab Δ k hk v i j` as an intermediate fact.

Rewrite `this` using `[← hu v]`. Conclude with `this`. Conclude with `⟨h, int_star h⟩`.
-/
theorem finG_cls {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {Δ : F} (hneg : ∀ σ : F →+* ℝ, σ Δ < 0)
    (ι : U3 Δ →* GA Δ) (hι : IsIotaG ι) :
    ∃ S : Finset (GA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u : GA Δ, (∀ v, u.1 v ∈ KU (Ov v) (cv v Δ)) ∧ g = ι γ * s * u := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 := hneg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  have hΔ : Δ ≠ 0 := by
    rintro rfl
    simp at h0
  haveI : Fact (∀ r : F, r ^ 2 ≠ Δ + 0 * r) := ⟨fun r hr => by
    rw [zero_mul, add_zero] at hr
    rw [← hr, map_pow] at h0
    exact absurd (sq_nonneg _) (not_le.2 h0)⟩
  obtain ⟨n, x, hx, -⟩ := unitary_class_set_finite F (Lsq F Δ) (sg Δ) 3 1 {x | ∀ i, IsIntegral ℤ (x i)} (fun _ => rfl) (emb_star Δ hneg)
    (fun τ => ⟨(Equiv.sumEmpty _ _).symm, 1, by
      rw [Matrix.map_one _ (map_zero τ) (map_one τ), Units.val_one, PI.UJClassFin.cT_one]
      ext (i | i) (j | j)
      · simp [PI.UJClassFin.Jpq, Matrix.one_apply]
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0⟩)
    ⟨1, one_ne_zero, fun x hx i => by simpa using hx i⟩
    ⟨1, one_ne_zero, fun i e he j => by by_cases h : j = i <;> simp [Pi.single_apply, h, he, isIntegral_zero]⟩
  choose l hl using exists_lift Δ hΔ
  obtain ⟨S, hS⟩ := cover_abs ι _ _ l (phi Δ)
    (fun v => (Matrix.unitaryGroup (Fin 3) (Lsq (Kv v) (cv v Δ))).subtype.comp ((rpg _ _).p v)) hl (exists_rat Δ ι hι) x hx
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, s, hs, u, ⟨k, hk, hu⟩, e⟩ := hS g
  refine ⟨γ, s, hs, u, fun v i j => ?_, e⟩
  have h : IsIntegral (Ov v) ((u.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) i j) := by
    have := int_of_stab Δ k hk v i j
    rw [← hu v] at this
    exact this
  exact ⟨h, int_star h⟩

end UpperTheory.V.Z.Sym.Glob
