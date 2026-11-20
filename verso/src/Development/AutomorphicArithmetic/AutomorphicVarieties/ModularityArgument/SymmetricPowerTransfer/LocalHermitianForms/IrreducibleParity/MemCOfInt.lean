import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.PS

open QuadraticAlgebra

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

variable (τ) in

def sc : Kˣ →* (Etau K τ)ˣ := Units.map (algebraMap K (Etau K τ) : K →* Etau K τ)

def nU : (Etau K τ)ˣ →* Kˣ := Units.map (QuadraticAlgebra.norm : Etau K τ →* K)

def ml (z : (Etau K τ)ˣ) (S : Set (Etau K τ)) : Set (Etau K τ) := ((z : Etau K τ) * ·) '' S

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_val (s : Kˣ) : (sc τ s : Etau K τ) = algebraMap K (Etau K τ) s := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nU_val (z : (Etau K τ)ˣ) : (nU z : K) = QuadraticAlgebra.norm (z : Etau K τ) := rfl

/- English proof (translation)
Use `ext`. Simplify using `[nU_val, sc_val]`.
-/
theorem nU_sc (s : Kˣ) : nU (sc τ s) = s ^ 2 := by
  ext; simp [nU_val, sc_val]

/- English proof (translation)
Simplify using `only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quo_mul (a b : (Etau K τ)ˣ) : quo (a * b) = quo a * quo b := by
  simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring

def qU (z : (Etau K τ)ˣ) : (Etau K τ)ˣ := z ^ 2 * sc τ (nU z⁻¹)

/- English proof (translation)
Establish `h : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1` using `Units.mul_inv z`. Simplify using `only [qU, Units.val_mul, Units.val_pow_eq_pow_val, sc_val, nU_val, algebraMap_norm_eq_mul_star, quo]`. Take the linear combination `((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * h`.
-/
theorem qU_val (z : (Etau K τ)ˣ) : (qU z : Etau K τ) = quo z := by
  have h : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := Units.mul_inv z
  simp only [qU, Units.val_mul, Units.val_pow_eq_pow_val, sc_val, nU_val, algebraMap_norm_eq_mul_star, quo]
  linear_combination ((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * h

/- English proof (translation)
Rewrite using `[qU, map_mul, map_pow, nU_sc, map_inv, ← mul_pow, mul_inv_cancel, one_pow]`.
-/
theorem nU_qU (z : (Etau K τ)ˣ) : nU (qU z) = 1 := by
  rw [qU, map_mul, map_pow, nU_sc, map_inv, ← mul_pow, mul_inv_cancel, one_pow]

/- English proof (translation)
Establish `hs : ∀ r : K, star (algebraMap K (Etau K τ) r) = algebraMap K (Etau K τ) r` using `fun r => by`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[quo, ← map_inv, sc_val, sc_val, hs, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem quo_sc (s : Kˣ) : quo (sc τ s) = 1 := by
  have hs : ∀ r : K, star (algebraMap K (Etau K τ) r) = algebraMap K (Etau K τ) r := fun r => by
    ext <;> simp
  rw [quo, ← map_inv, sc_val, sc_val, hs, ← map_mul]
  simp

/- English proof (translation)
Use `show IsIntegral O (quo (sc τ s)) ∧ IsIntegral O (quo (sc τ s)⁻¹)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[quo_sc]`. Conclude with `isIntegral_one`. Rewrite using `[← map_inv, quo_sc]`.

Conclude with `isIntegral_one`.
-/
theorem sc_mem (s : Kˣ) : sc τ s ∈ Cint O τ := by
  show IsIntegral O (quo (sc τ s)) ∧ IsIntegral O (quo (sc τ s)⁻¹)
  refine ⟨?_, ?_⟩
  · rw [quo_sc]
    exact isIntegral_one
  · rw [← map_inv, quo_sc]
    exact isIntegral_one

/- English proof (translation)
Set `f : Etau K τ →ₐ[O] Etau K τ` to `{ starRingEnd (Etau K τ) with commutes' := fun r => by show star (algebraMap O (Etau K τ) r) = algebraMap O (Etau K τ) r`. Rewrite using `[IsScalarTower.algebraMap_apply O K (Etau K τ)]`. Apply the tactic sequence `ext <;> simp }`. Conclude with `h.map f`.
-/
theorem star_int {x : Etau K τ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Etau K τ →ₐ[O] Etau K τ :=
    { starRingEnd (Etau K τ) with
      commutes' := fun r => by
        show star (algebraMap O (Etau K τ) r) = algebraMap O (Etau K τ) r
        rw [IsScalarTower.algebraMap_apply O K (Etau K τ)]
        ext <;> simp }
  exact h.map f

/- English proof (translation)
Use `⟨h.mul (star_int h'), ?_⟩` and prove the remaining obligations. Use `show IsIntegral O (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (((z⁻¹⁻¹ : (Etau K τ)ˣ)) : Etau K τ))`. Rewrite using `[inv_inv]`. Conclude with `h'.mul (star_int h)`.
-/
theorem mem_C_of_int {z : (Etau K τ)ˣ} (h : IsIntegral O (z : Etau K τ))
    (h' : IsIntegral O ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) : z ∈ Cint O τ := by
  refine ⟨h.mul (star_int h'), ?_⟩
  show IsIntegral O (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (((z⁻¹⁻¹ : (Etau K τ)ˣ)) : Etau K τ))
  rw [inv_inv]
  exact h'.mul (star_int h)

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨IsIntegral.of_pow (n := 2) (by norm_num) ?_, IsIntegral.of_pow (n := 2) (by norm_num) ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, ← quo_mul, ← pow_two]` and apply the resulting hypothesis. Rewrite using `[pow_two, ← quo_mul, ← pow_two]`. Rewrite `h2` using `[← inv_pow]`. Then use the resulting hypothesis.
-/
theorem mem_C_of_sq {z : (Etau K τ)ˣ} (h : z ^ 2 ∈ Cint O τ) : z ∈ Cint O τ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨IsIntegral.of_pow (n := 2) (by norm_num) ?_, IsIntegral.of_pow (n := 2) (by norm_num) ?_⟩
  · rwa [pow_two, ← quo_mul, ← pow_two]
  · rw [pow_two, ← quo_mul, ← pow_two]
    rwa [← inv_pow] at h2

/- English proof (translation)
The claim follows from `mul_mem (pow_mem h 2) (sc_mem _)`.
-/
theorem qU_mem {z : (Etau K τ)ˣ} (h : z ∈ Cint O τ) : qU z ∈ Cint O τ :=
  mul_mem (pow_mem h 2) (sc_mem _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[Units.inv_mul_cancel_left]` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨_, h, Units.mul_inv_cancel_left z w⟩`.
-/
theorem mem_ml {z : (Etau K τ)ˣ} {S : Set (Etau K τ)} {w : Etau K τ} :
    w ∈ ml z S ↔ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [Units.inv_mul_cancel_left]
  · intro h
    exact ⟨_, h, Units.mul_inv_cancel_left z w⟩

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[mem_ml, mem_ml, mem_ml, mul_inv_rev, Units.val_mul, mul_assoc]`.
-/
theorem ml_mul (a b : (Etau K τ)ˣ) (S : Set (Etau K τ)) : ml (a * b) S = ml a (ml b S) := by
  ext w
  rw [mem_ml, mem_ml, mem_ml, mul_inv_rev, Units.val_mul, mul_assoc]

/- English proof (translation)
Use extensionality with `w`. Simplify using `[mem_ml]`.
-/
theorem ml_one (S : Set (Etau K τ)) : ml 1 S = S := by
  ext w; simp [mem_ml]

/- English proof (translation)
Apply `mem_C_of_int` to reduce the goal to its premises. Simplify using `using h.2 _ h'.1`. Simplify `h'.2 _ h.1` using `[mul_inv_rev]`.
-/
theorem gen_uniq {S : Set (Etau K τ)} {y y' : (Etau K τ)ˣ} (h : Gen O τ S y) (h' : Gen O τ S y') :
    y⁻¹ * y' ∈ Cint O τ := by
  apply mem_C_of_int
  · simpa using h.2 _ h'.1
  · simpa [mul_inv_rev] using h'.2 _ h.1

/- English proof (translation)
Use `⟨⟨_, h.1, (Units.val_mul z y).symm⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]`. Conclude with `h.2 x hx`.
-/
theorem gen_ml {S : Set (Etau K τ)} {y : (Etau K τ)ˣ} (h : Gen O τ S y) (z : (Etau K τ)ˣ) :
    Gen O τ (ml z S) (z * y) := by
  refine ⟨⟨_, h.1, (Units.val_mul z y).symm⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  exact h.2 x hx

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Use `⟨s.image ((z : Etau K τ) * ·), ?_⟩` and prove the remaining obligations. Establish `e : ((z : Etau K τ) * ·) = ⇑(LinearMap.mulLeft O (z : Etau K τ))` using `rfl`. Rewrite using `[Finset.coe_image, e, ← Submodule.map_span, Submodule.map_coe]`. Both sides reduce to the same expression.
-/
theorem fg_ml {S : Set (Etau K τ)} (h : ∃ s : Finset (Etau K τ), S = Submodule.span O (s : Set (Etau K τ)))
    (z : (Etau K τ)ˣ) : ∃ s : Finset (Etau K τ), ml z S = Submodule.span O (s : Set (Etau K τ)) := by
  classical
  obtain ⟨s, rfl⟩ := h
  refine ⟨s.image ((z : Etau K τ) * ·), ?_⟩
  have e : ((z : Etau K τ) * ·) = ⇑(LinearMap.mulLeft O (z : Etau K τ)) := rfl
  rw [Finset.coe_image, e, ← Submodule.map_span, Submodule.map_coe]
  rfl

/- English proof (translation)
Use `⟨fg_ml h.fg z, ?_⟩` and prove the remaining obligations. Establish `e : ml z S = ⇑(LinearMap.mulLeft K (z : Etau K τ)) '' S` using `rfl`. Rewrite using `[e, ← Submodule.map_span, h.span, Submodule.map_top, LinearMap.range_eq_top]`. Introduce `w`. Conclude with `⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w, by simp⟩`.
-/
theorem lat_ml {S : Set (Etau K τ)} (h : IsLat O τ S) (z : (Etau K τ)ˣ) : IsLat O τ (ml z S) := by
  refine ⟨fg_ml h.fg z, ?_⟩
  have e : ml z S = ⇑(LinearMap.mulLeft K (z : Etau K τ)) '' S := rfl
  rw [e, ← Submodule.map_span, h.span, Submodule.map_top, LinearMap.range_eq_top]
  intro w
  exact ⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w, by simp⟩

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨ω * x, h x hx, by dsimp only; ring⟩`.
-/
theorem stab_ml {S : Set (Etau K τ)} (h : ∀ y ∈ S, ω * y ∈ S) (z : (Etau K τ)ˣ) : ∀ y ∈ ml z S, ω * y ∈ ml z S := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨ω * x, h x hx, by dsimp only; ring⟩

/- English proof (translation)
Establish `key : ∀ x y : Etau K τ, t * (nU z : K) * (x * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y)).im = t * (((z : Etau K τ) * x) * star y).im`. Introduce `x y`. Establish `hz : star (z : Etau K τ) * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = 1`. Rewrite using `[← star_mul, Units.inv_mul, star_one]`. Establish `e1 : ((z : Etau K τ) * x) * star y = algebraMap K (Etau K τ) (nU z) * (x * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y))`.

Rewrite using `[nU_val, algebraMap_norm_eq_mul_star, star_mul]`. Take the linear combination `(-((z : Etau K τ) * x * star y)) * hz`. Rewrite using `[e1]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fg_ml h.fg z, fun y => ?_, stab_ml h.stab z⟩` and prove the remaining obligations. Rewrite using `[mem_ml, h.dual]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `H _ ⟨x, hx, rfl⟩ dsimp only`. Rewrite using `[← key x y]`.

Conclude with `H x hx`. Introduce `H x hx`. Rewrite using `[key x y]`. Conclude with `H _ ⟨x, hx, rfl⟩`.
-/
theorem fix_ml {S : Set (Etau K τ)} {t : K} (z : (Etau K τ)ˣ) (h : IsFixP O τ (t * nU z) S) : IsFixP O τ t (ml z S) := by
  have key : ∀ x y : Etau K τ, t * (nU z : K) * (x * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y)).im
      = t * (((z : Etau K τ) * x) * star y).im := by
    intro x y
    have hz : star (z : Etau K τ) * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = 1 := by
      rw [← star_mul, Units.inv_mul, star_one]
    have e1 : ((z : Etau K τ) * x) * star y
        = algebraMap K (Etau K τ) (nU z) * (x * star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y)) := by
      rw [nU_val, algebraMap_norm_eq_mul_star, star_mul]
      linear_combination (-((z : Etau K τ) * x * star y)) * hz
    rw [e1]
    simp
    ring
  refine ⟨fg_ml h.fg z, fun y => ?_, stab_ml h.stab z⟩
  rw [mem_ml, h.dual]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    dsimp only
    rw [← key x y]
    exact H x hx
  · intro H x hx
    rw [key x y]
    exact H _ ⟨x, hx, rfl⟩

/- English proof (translation)
Use `⟨h.fg, fun y => ?_, h.stab⟩` and prove the remaining obligations. Rewrite using `[h.dual]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations. Establish `e : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Conclude with `⟨(ε : O) * r, by rw [map_mul, hr]; ring⟩`. Introduce and unpack `⟨r, hr⟩`. Use `⟨((ε⁻¹ : Oˣ) : O) * r, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hr]`. Take the linear combination `(t * (x * star y).im) * e`.
-/
theorem fix_unit {S : Set (Etau K τ)} {t : K} (ε : Oˣ) (h : IsFixP O τ t S) : IsFixP O τ (algebraMap O K ε * t) S := by
  refine ⟨h.fg, fun y => ?_, h.stab⟩
  rw [h.dual]
  refine forall₂_congr fun x _ => ?_
  have e : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨(ε : O) * r, by rw [map_mul, hr]; ring⟩
  · rintro ⟨r, hr⟩
    refine ⟨((ε⁻¹ : Oˣ) : O) * r, ?_⟩
    rw [map_mul, hr]
    linear_combination (t * (x * star y).im) * e

/- English proof (translation)
Take `⟨f, rfl⟩` from `h`. Use extensionality with `w`. Establish `e : (((sc τ s)⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w = (ε⁻¹ : Oˣ) • w`. Rewrite using `[Units.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply O K (Etau K τ), map_units_inv, hs, ← map_inv, sc_val, Units.val_inv_eq_inv_val]`. Rewrite using `[mem_ml, e]`.

Conclude with `Submodule.smul_mem_iff' _ _`.
-/
theorem ml_unit {S : Set (Etau K τ)} (h : ∃ s : Finset (Etau K τ), S = Submodule.span O (s : Set (Etau K τ)))
    (ε : Oˣ) (s : Kˣ) (hs : algebraMap O K ε = s) : ml (sc τ s) S = S := by
  obtain ⟨f, rfl⟩ := h
  ext w
  have e : (((sc τ s)⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w = (ε⁻¹ : Oˣ) • w := by
    rw [Units.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply O K (Etau K τ), map_units_inv, hs,
      ← map_inv, sc_val, Units.val_inv_eq_inv_val]
  rw [mem_ml, e]
  exact Submodule.smul_mem_iff' _ _

/- English proof (translation)
Establish `e : ∀ s : Kˣ, ml (sc τ s) S = (fun x => (s : K) • x) '' S` using `fun s => by`. Simplify using `only [ml, sc_val, Algebra.smul_def]`. Use `show (∃ s : Kˣ, S' = _) ↔ _`. Conclude with `exists_congr fun s => by rw [e]`.
-/
theorem mem_cls {S S' : Set (Etau K τ)} : S' ∈ cls τ S ↔ ∃ s : Kˣ, S' = ml (sc τ s) S := by
  have e : ∀ s : Kˣ, ml (sc τ s) S = (fun x => (s : K) • x) '' S := fun s => by
    simp only [ml, sc_val, Algebra.smul_def]
  show (∃ s : Kˣ, S' = _) ↔ _
  exact exists_congr fun s => by rw [e]

/- English proof (translation)
Use extensionality with `S'`. Rewrite using `[mem_cls, mem_cls]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨u * s, by rw [hu, map_mul, ml_mul]⟩`.

Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨u * s⁻¹, by rw [hu, ← ml_mul, ← map_mul, inv_mul_cancel_right]⟩`.
-/
theorem cls_sc (s : Kˣ) (S : Set (Etau K τ)) : cls τ (ml (sc τ s) S) = cls τ S := by
  ext S'
  rw [mem_cls, mem_cls]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u * s, by rw [hu, map_mul, ml_mul]⟩
  · rintro ⟨u, hu⟩
    exact ⟨u * s⁻¹, by rw [hu, ← ml_mul, ← map_mul, inv_mul_cancel_right]⟩

/- English proof (translation)
Establish `hS : S ∈ cls τ S` using `mem_cls.2 ⟨1, by rw [map_one, ml_one]⟩`. Rewrite `hS` using `[h]`. Conclude with `mem_cls.1 hS`.
-/
theorem cls_eq {S S' : Set (Etau K τ)} (h : cls τ S = cls τ S') : ∃ s : Kˣ, S = ml (sc τ s) S' := by
  have hS : S ∈ cls τ S := mem_cls.2 ⟨1, by rw [map_one, ml_one]⟩
  rw [h] at hS
  exact mem_cls.1 hS

/- English proof (translation)
Use extensionality with `S'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨T, hT, rfl⟩`. Take `⟨s, rfl⟩` from `mem_cls.1 hT`. Conclude with `mem_cls.2 ⟨s, by rw [← ml_mul, ← ml_mul, mul_comm]⟩`.

Introduce `hS'`. Take `⟨s, rfl⟩` from `mem_cls.1 hS'`. Conclude with `⟨ml (sc τ s) S, mem_cls.2 ⟨s, rfl⟩, by rw [← ml_mul, ← ml_mul, mul_comm]⟩`.
-/
theorem cls_ml (z : (Etau K τ)ˣ) (S : Set (Etau K τ)) : ml z '' cls τ S = cls τ (ml z S) := by
  ext S'
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨s, rfl⟩ := mem_cls.1 hT
    exact mem_cls.2 ⟨s, by rw [← ml_mul, ← ml_mul, mul_comm]⟩
  · intro hS'
    obtain ⟨s, rfl⟩ := mem_cls.1 hS'
    exact ⟨ml (sc τ s) S, mem_cls.2 ⟨s, rfl⟩, by rw [← ml_mul, ← ml_mul, mul_comm]⟩

variable [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨f, hf⟩` from `h.fg`. Establish `hB : ∀ w ∈ S, ∀ v ∈ S, 2 * w.re * v.re + τ * (w.re * v.im + w.im * v.re) + 2 * w.im * v.im = 0`. Introduce `w hw v hv`.

Establish `hwv : w + v ∈ S`. Rewrite `hw`, `hv`, the goal using `[hf]`. Conclude with `add_mem hw hv`. Establish `e1` using `hc w hw`. Establish `e2` using `hc v hv`.

Establish `e3` using `hc _ hwv`. Simplify using `only [norm_def, re_add, im_add] at e1 e2 e3`. Take the linear combination `e3 - e1 - e2`. Establish `hall : ∀ x ∈ Submodule.span K S, ∀ v ∈ S, 2 * x.re * v.re + τ * (x.re * v.im + x.im * v.re) + 2 * x.im * v.im = 0`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hB x hx`. Consider the case `zero => intro v _`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `v hv`. Simplify using `only [re_add, im_add]`. Take the linear combination `hx v hv + hy v hv`. Consider the case `smul c x _ hx`. Introduce `v hv`.

Simplify using `only [re_smul, im_smul, smul_eq_mul]`. Take the linear combination `c * hx v hv`. Rewrite `hall` using `[h.span]`. Establish `key : ∀ w ∈ S, w = 0`. Introduce `w hw`.

Establish `e1` using `hall 1 Submodule.mem_top w hw`. Establish `e2` using `hall ω Submodule.mem_top w hw`. Simplify using `only [re_one, im_one, omega_re, omega_im] at e1 e2`. Establish `him : w.im = 0`. Establish `e : (τ ^ 2 - 4) * w.im = 0` using `by linear_combination τ * e1 - 2 * e2`.

Conclude with `(mul_eq_zero.1 e).resolve_left hτ`. Establish `hre : w.re = 0`. Establish `e : 2 * w.re = 0` using `by linear_combination e1 - τ * him`. Conclude with `(mul_eq_zero.1 e).resolve_left h2`. Apply the tactic sequence `ext <;> simp [hre, him]`.

Establish `hbot : Submodule.span K S = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Conclude with `key`. Rewrite `hbot` using `[h.span]`. Conclude with `top_ne_bot hbot`.
-/
private theorem exists_norm_ne_zero_of_isLat {S : Set (Etau K τ)} (hτ : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0)
    (h : IsLat O τ S) : ∃ w ∈ S, QuadraticAlgebra.norm w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨f, hf⟩ := h.fg
  have hB : ∀ w ∈ S, ∀ v ∈ S,
      2 * w.re * v.re + τ * (w.re * v.im + w.im * v.re) + 2 * w.im * v.im = 0 := by
    intro w hw v hv
    have hwv : w + v ∈ S := by
      rw [hf] at hw hv ⊢
      exact add_mem hw hv
    have e1 := hc w hw
    have e2 := hc v hv
    have e3 := hc _ hwv
    simp only [norm_def, re_add, im_add] at e1 e2 e3
    linear_combination e3 - e1 - e2
  have hall : ∀ x ∈ Submodule.span K S, ∀ v ∈ S,
      2 * x.re * v.re + τ * (x.re * v.im + x.im * v.re) + 2 * x.im * v.im = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hB x hx
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      simp only [re_add, im_add]
      linear_combination hx v hv + hy v hv
    | smul c x _ hx =>
      intro v hv
      simp only [re_smul, im_smul, smul_eq_mul]
      linear_combination c * hx v hv
  rw [h.span] at hall
  have key : ∀ w ∈ S, w = 0 := by
    intro w hw
    have e1 := hall 1 Submodule.mem_top w hw
    have e2 := hall ω Submodule.mem_top w hw
    simp only [re_one, im_one, omega_re, omega_im] at e1 e2
    have him : w.im = 0 := by
      have e : (τ ^ 2 - 4) * w.im = 0 := by linear_combination τ * e1 - 2 * e2
      exact (mul_eq_zero.1 e).resolve_left hτ
    have hre : w.re = 0 := by
      have e : 2 * w.re = 0 := by linear_combination e1 - τ * him
      exact (mul_eq_zero.1 e).resolve_left h2
    ext <;> simp [hre, him]
  have hbot : Submodule.span K S = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact key
  rw [h.span] at hbot
  exact top_ne_bot hbot

/- English proof (translation)
Take `⟨n, hn⟩` from `h1`. Take `⟨m, hm⟩` from `h2`. Use `⟨Polynomial.X ^ 2 - Polynomial.C (m - n - 1) * Polynomial.X + Polynomial.C n, by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, IsScalarTower.algebraMap_apply O K (Etau K τ), map_sub, map_one, hn, hm, algebraMap_norm_eq_mul_star, star_add, star_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem isIntegral_of_norm_and_norm_add_one_integral {x : Etau K τ} (h1 : QuadraticAlgebra.norm x ∈ (algebraMap O K).range)
    (h2 : QuadraticAlgebra.norm (x + 1) ∈ (algebraMap O K).range) : IsIntegral O x := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (m - n - 1) * Polynomial.X + Polynomial.C n, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, IsScalarTower.algebraMap_apply O K (Etau K τ), map_sub,
    map_one, hn, hm, algebraMap_norm_eq_mul_star, star_add, star_one]
  ring

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (insert τ (f.image (fun x : Etau K τ => x.re) ∪ f.image (fun x : Etau K τ => x.im)))`. Use `⟨(b : O) ^ 3, pow_ne_zero 3 (nonZeroDivisors.ne_zero b.2), ?_⟩` and prove the remaining obligations. Establish `hint : ∀ w ∈ Submodule.span O (f : Set (Etau K τ)), IsLocalization.IsInteger O ((b : O) • w.re) ∧ IsLocalization.IsInteger O ((b : O) • w.im)`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Conclude with `⟨hb _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))), hb _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)))⟩`. Consider the case `zero => simp [IsLocalization.isInteger_zero]`. Consider the case `add x y _ _ hx hy`. Rewrite using `[re_add, im_add, smul_add, smul_add]`.

Conclude with `⟨IsLocalization.isInteger_add hx.1 hy.1, IsLocalization.isInteger_add hx.2 hy.2⟩`. Consider the case `smul c x _ hx`. Rewrite using `[re_smul, im_smul, smul_comm, smul_comm (b : O) c x.im]`. Conclude with `⟨IsLocalization.isInteger_smul hx.1, IsLocalization.isInteger_smul hx.2⟩`. Introduce `w hw`.

Take `⟨⟨p, hp⟩, ⟨q, hq⟩⟩` from `hint w hw`. Take `⟨u, hu⟩` from `hb τ (Finset.mem_insert_self _ _)`. Use `⟨(b : O) * p * p + u * p * q + (b : O) * q * q, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, hp, hq, hu, Algebra.smul_def, norm_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_denominator_norm_span_finset [IsFractionRing O K] (f : Finset (Etau K τ)) :
    ∃ d : O, d ≠ 0 ∧ ∀ w ∈ Submodule.span O (f : Set (Etau K τ)),
      algebraMap O K d * QuadraticAlgebra.norm w ∈ (algebraMap O K).range := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (insert τ (f.image (fun x : Etau K τ => x.re) ∪ f.image (fun x : Etau K τ => x.im)))
  refine ⟨(b : O) ^ 3, pow_ne_zero 3 (nonZeroDivisors.ne_zero b.2), ?_⟩
  have hint : ∀ w ∈ Submodule.span O (f : Set (Etau K τ)),
      IsLocalization.IsInteger O ((b : O) • w.re) ∧ IsLocalization.IsInteger O ((b : O) • w.im) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      exact ⟨hb _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))),
        hb _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)))⟩
    | zero => simp [IsLocalization.isInteger_zero]
    | add x y _ _ hx hy =>
      rw [re_add, im_add, smul_add, smul_add]
      exact ⟨IsLocalization.isInteger_add hx.1 hy.1, IsLocalization.isInteger_add hx.2 hy.2⟩
    | smul c x _ hx =>
      rw [re_smul, im_smul, smul_comm, smul_comm (b : O) c x.im]
      exact ⟨IsLocalization.isInteger_smul hx.1, IsLocalization.isInteger_smul hx.2⟩
  intro w hw
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hint w hw
  obtain ⟨u, hu⟩ := hb τ (Finset.mem_insert_self _ _)
  refine ⟨(b : O) * p * p + u * p * q + (b : O) * q * q, ?_⟩
  simp only [map_add, map_mul, map_pow, hp, hq, hu, Algebra.smul_def, norm_def]
  ring

/- English proof (translation)
Use `haveI := L.frac`. Establish `h2 : (2 : K) ≠ 0`. Establish `e` using `L.two.map (algebraMap O K)`. Rewrite `e` using `[map_ofNat]`. Conclude with `e.ne_zero`.

Take `⟨f, hf⟩` from `h.fg`. Take `⟨d, hd0, hd⟩` from `exists_denominator_norm_span_finset (O := O) (τ := τ) f`. Establish `hinj` using `IsFractionRing.injective O K`. Establish `hdK : algebraMap O K d ≠ 0` using `(map_ne_zero_iff _ hinj).2 hd0`. Establish `hS : ∀ w ∈ S, w ∈ Submodule.span O (f : Set (Etau K τ))`.

Introduce `w hw`. Rewrite `hw` using `[hf]`. Conclude with `hw`. Take `⟨w0, hw0, hN0⟩` from `exists_norm_ne_zero_of_isLat hτ h2 h`. Establish `hTne : (IsDiscreteValuationRing.addVal O '' {a : O | a ≠ 0 ∧ ∃ w ∈ S, algebraMap O K a = algebraMap O K d * QuadraticAlgebra.norm w}).Nonempty`.

Take `⟨a, ha⟩` from `hd w0 (hS w0 hw0)`. Use `⟨_, a, ⟨?_, w0, hw0, ha⟩, rfl⟩` and prove the remaining obligations. Introduce `ha0`. Rewrite `ha` using `[ha0, map_zero]`. Conclude with `mul_ne_zero hdK hN0 ha.symm`.

Take `⟨_, ⟨a, ⟨ha0, y, hy, hay⟩, rfl⟩, hmin⟩` from `WellFounded.has_min wellFounded_lt _ hTne`. Establish `hNy : QuadraticAlgebra.norm y ≠ 0`. Introduce `h0`. Rewrite `hay` using `[h0, mul_zero]`. Conclude with `ha0 ((map_eq_zero_iff _ hinj).1 hay)`.

Use `⟨y, hy, hNy, fun w hw => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hNw : QuadraticAlgebra.norm w = 0`. Conclude with `⟨0, by rw [hNw, zero_div, map_zero]⟩`. Take `⟨b, hb⟩` from `hd w (hS w hw)`. Establish `hb0 : b ≠ 0`.

Introduce `hb0`. Rewrite `hb` using `[hb0, map_zero]`. Conclude with `mul_ne_zero hdK hNw hb.symm`. Establish `hle : IsDiscreteValuationRing.addVal O a ≤ IsDiscreteValuationRing.addVal O b` using `not_lt.1 (hmin _ ⟨b, ⟨hb0, w, hw, hb⟩, rfl⟩)`. Take `⟨c, rfl⟩` from `IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[map_mul]`. Rewrite using `[eq_div_iff hNy]`. Apply `mul_left_cancel₀ hdK` to reduce the goal to its premises. Take the linear combination `hb - (algebraMap O K c) * hay`.
-/
private theorem exists_norm_ne_zero_norm_div_integral_of_isLat {Δ : K} (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {S : Set (Etau K τ)}
    (h : IsLat O τ S) : ∃ y ∈ S, QuadraticAlgebra.norm y ≠ 0 ∧
      ∀ w ∈ S, QuadraticAlgebra.norm w / QuadraticAlgebra.norm y ∈ (algebraMap O K).range := by
  haveI := L.frac
  have h2 : (2 : K) ≠ 0 := by
    have e := L.two.map (algebraMap O K)
    rw [map_ofNat] at e
    exact e.ne_zero
  obtain ⟨f, hf⟩ := h.fg
  obtain ⟨d, hd0, hd⟩ := exists_denominator_norm_span_finset (O := O) (τ := τ) f
  have hinj := IsFractionRing.injective O K
  have hdK : algebraMap O K d ≠ 0 := (map_ne_zero_iff _ hinj).2 hd0
  have hS : ∀ w ∈ S, w ∈ Submodule.span O (f : Set (Etau K τ)) := by
    intro w hw
    rw [hf] at hw
    exact hw
  obtain ⟨w0, hw0, hN0⟩ := exists_norm_ne_zero_of_isLat hτ h2 h
  have hTne : (IsDiscreteValuationRing.addVal O ''
      {a : O | a ≠ 0 ∧ ∃ w ∈ S, algebraMap O K a = algebraMap O K d * QuadraticAlgebra.norm w}).Nonempty := by
    obtain ⟨a, ha⟩ := hd w0 (hS w0 hw0)
    refine ⟨_, a, ⟨?_, w0, hw0, ha⟩, rfl⟩
    intro ha0
    rw [ha0, map_zero] at ha
    exact mul_ne_zero hdK hN0 ha.symm
  obtain ⟨_, ⟨a, ⟨ha0, y, hy, hay⟩, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt _ hTne
  have hNy : QuadraticAlgebra.norm y ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hay
    exact ha0 ((map_eq_zero_iff _ hinj).1 hay)
  refine ⟨y, hy, hNy, fun w hw => ?_⟩
  by_cases hNw : QuadraticAlgebra.norm w = 0
  · exact ⟨0, by rw [hNw, zero_div, map_zero]⟩
  obtain ⟨b, hb⟩ := hd w (hS w hw)
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, map_zero] at hb
    exact mul_ne_zero hdK hNw hb.symm
  have hle : IsDiscreteValuationRing.addVal O a ≤ IsDiscreteValuationRing.addVal O b :=
    not_lt.1 (hmin _ ⟨b, ⟨hb0, w, hw, hb⟩, rfl⟩)
  obtain ⟨c, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle
  refine ⟨c, ?_⟩
  rw [map_mul] at hb
  rw [eq_div_iff hNy]
  apply mul_left_cancel₀ hdK
  linear_combination hb - (algebraMap O K c) * hay

/- English proof (translation)
Take `⟨y, hy, hNy, hdiv⟩` from `exists_norm_ne_zero_norm_div_integral_of_isLat L hτ h`. Establish `hu : IsUnit y` using `isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hNy)`. Establish `hadd : ∀ w ∈ S, w + y ∈ S`. Introduce `w hw`. Take `⟨f, hf⟩` from `h.fg`.

Rewrite `hw`, `hy`, the goal using `[hf]`. Conclude with `add_mem hw hy`. Use `⟨hu.unit, ⟨hy, fun w hw => ?_⟩⟩` and prove the remaining obligations. Apply `isIntegral_of_norm_and_norm_add_one_integral` to reduce the goal to its premises. Rewrite using `[map_mul, map_units_inv, IsUnit.unit_spec, inv_mul_eq_div]`.

Conclude with `hdiv w hw`. Establish `e : ((hu.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w + 1 = ((hu.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (w + y)`. Rewrite using `[mul_add, IsUnit.val_inv_mul]`. Rewrite using `[e, map_mul, map_units_inv, IsUnit.unit_spec, inv_mul_eq_div]`. Conclude with `hdiv _ (hadd w hw)`.
-/
theorem gen_ex {Δ : K} (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {S : Set (Etau K τ)} (h : IsLat O τ S) :
    ∃ y, Gen O τ S y := by
  obtain ⟨y, hy, hNy, hdiv⟩ := exists_norm_ne_zero_norm_div_integral_of_isLat L hτ h
  have hu : IsUnit y := isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hNy)
  have hadd : ∀ w ∈ S, w + y ∈ S := by
    intro w hw
    obtain ⟨f, hf⟩ := h.fg
    rw [hf] at hw hy ⊢
    exact add_mem hw hy
  refine ⟨hu.unit, ⟨hy, fun w hw => ?_⟩⟩
  apply isIntegral_of_norm_and_norm_add_one_integral
  · rw [map_mul, map_units_inv, IsUnit.unit_spec, inv_mul_eq_div]
    exact hdiv w hw
  · have e : ((hu.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w + 1
        = ((hu.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (w + y) := by
      rw [mul_add, IsUnit.val_inv_mul]
    rw [e, map_mul, map_units_inv, IsUnit.unit_spec, inv_mul_eq_div]
    exact hdiv _ (hadd w hw)

/- English proof (translation)
Use `haveI := L.frac`. Take `⟨f, rfl⟩` from `h.fg`. Establish `star_sm : ∀ (c : K) (w : Etau K τ), star (c • w) = c • star w`. Introduce `c w`. Apply the tactic sequence `ext <;> simp <;> ring`.

Establish `hmem : ∀ w ∈ (Submodule.span O (f : Set (Etau K τ))), (t' / t) • w ∈ Submodule.span O (f : Set (Etau K τ))`. Introduce `w hw`. Establish `hw'` using `(h'.dual w).1 hw`. Use `show (t' / t) • w ∈ ((Submodule.span O (f : Set (Etau K τ)) : Set (Etau K τ)))`. Rewrite using `[h.dual]`.

Introduce `x hx`. Establish `e : t * (x * star ((t' / t) • w)).im = t' * (x * star w).im`. Rewrite using `[star_sm, mul_smul_comm]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `hw' x hx`. Establish `hne : Submodule.span O (f : Set (Etau K τ)) ≠ ⊥`. Introduce `hb`. Establish `h1 : (1 : Etau K τ) ∈ ((Submodule.span O (f : Set (Etau K τ)) : Set (Etau K τ)))`.

Rewrite using `[h.dual]`. Introduce `x hx`. Rewrite `hx` using `[hb]`. Simplify using `at hx`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Rewrite `h1` using `[hb]`. Simplify using `at h1`. Establish `hint : IsIntegral O (t' / t)` using `isIntegral_of_smul_mem_submodule _ hne ⟨f, rfl⟩ _ hmem`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`.

Conclude with `⟨r, by rw [hr]; field_simp⟩`.
-/
theorem fix_div {Δ : K} (L : IsLoc O Δ) {S : Set (Etau K τ)} {t t' : K} {y : (Etau K τ)ˣ} (hy : Gen O τ S y)
    (h : IsFixP O τ t S) (h' : IsFixP O τ t' S) (ht : t ≠ 0) : ∃ r : O, t' = algebraMap O K r * t := by
  haveI := L.frac
  obtain ⟨f, rfl⟩ := h.fg
  have star_sm : ∀ (c : K) (w : Etau K τ), star (c • w) = c • star w := by
    intro c w
    ext <;> simp <;> ring
  have hmem : ∀ w ∈ (Submodule.span O (f : Set (Etau K τ))), (t' / t) • w ∈ Submodule.span O (f : Set (Etau K τ)) := by
    intro w hw
    have hw' := (h'.dual w).1 hw
    show (t' / t) • w ∈ ((Submodule.span O (f : Set (Etau K τ)) : Set (Etau K τ)))
    rw [h.dual]
    intro x hx
    have e : t * (x * star ((t' / t) • w)).im = t' * (x * star w).im := by
      rw [star_sm, mul_smul_comm]
      simp
      field_simp
    rw [e]
    exact hw' x hx
  have hne : Submodule.span O (f : Set (Etau K τ)) ≠ ⊥ := by
    intro hb
    have h1 : (1 : Etau K τ) ∈ ((Submodule.span O (f : Set (Etau K τ)) : Set (Etau K τ))) := by
      rw [h.dual]
      intro x hx
      rw [hb] at hx
      simp at hx
      subst hx
      simp
    rw [hb] at h1
    simp at h1
  have hint : IsIntegral O (t' / t) :=
    isIntegral_of_smul_mem_submodule _ hne ⟨f, rfl⟩ _ hmem
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨r, by rw [hr]; field_simp⟩

/- English proof (translation)
Use `haveI := L.frac`. Take `⟨r, hr⟩` from `fix_div L hy h h' ht`. Take `⟨r', hr'⟩` from `fix_div L hy h' h ht'`. Establish `e : algebraMap O K (r * r') = 1`. Rewrite using `[map_mul]`.

Apply `mul_right_cancel₀ ht` to reduce the goal to its premises. Rewrite `hr'` using `[hr]`. Take the linear combination `-hr'`. Establish `e2 : r * r' = 1` using `IsFractionRing.injective O K (by rw [e, map_one])`. Conclude with `⟨⟨r, r', e2, by rw [mul_comm]; exact e2⟩, hr⟩`.
-/
theorem fix_uniq {Δ : K} (L : IsLoc O Δ) {S : Set (Etau K τ)} {t t' : K} {y : (Etau K τ)ˣ} (hy : Gen O τ S y)
    (h : IsFixP O τ t S) (h' : IsFixP O τ t' S) (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ ε : Oˣ, t' = algebraMap O K ε * t := by
  haveI := L.frac
  obtain ⟨r, hr⟩ := fix_div L hy h h' ht
  obtain ⟨r', hr'⟩ := fix_div L hy h' h ht'
  have e : algebraMap O K (r * r') = 1 := by
    rw [map_mul]
    apply mul_right_cancel₀ ht
    rw [hr] at hr'
    linear_combination -hr'
  have e2 : r * r' = 1 := IsFractionRing.injective O K (by rw [e, map_one])
  exact ⟨⟨r, r', e2, by rw [mul_comm]; exact e2⟩, hr⟩

end UpperTheory.V.Z.Sym.Loc.PS
