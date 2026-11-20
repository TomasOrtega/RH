import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.ContinuousEF

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiC

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

def Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Subalgebra k (Matrix (Fin (n * d)) (Fin (n * d)) k) :=
  { toSubsemiring := Z.toSubsemiring.map (φ B)
    algebraMap_mem' := fun a => ⟨algebraMap k _ (a ^ p ^ c), Z.algebraMap_mem _, φ_scal B a⟩ }

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    ((Z' B Z : Subalgebra k _) : Set (Matrix (Fin (n * d)) (Fin (n * d)) k)) = φ B '' (Z : Set (Matrix (Fin n) (Fin n) k)) :=
  rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [eI, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]`.
-/
theorem eI_add (w w' : Fin (n * d) → k) : eI B (w + w') = eI B w + eI B w' := by
  funext i
  simp only [eI, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `hsm : ∀ (b : k) (v : Fin n → k), b • v = algebraMap k (Matrix (Fin n) (Fin n) k) b *ᵥ v`. Introduce `b v`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]`. Set `L : (Fin n → k) →ₗ[k] (Fin n → k)` to `{ toFun := fun v => eI B (y *ᵥ eF B v) map_add' := fun v v' => by`. Simplify using `only [eF_add, Matrix.mulVec_add, eI_add]`.

Use the proof step `map_smul' := fun b v => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[hsm b v, hsm b (eI B (y *ᵥ eF B v)), ← φ_apply_mulVec B _ v, Matrix.mulVec_mulVec, ← hy b, ← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [← eF_eI B (y *ᵥ eF B v), φ_apply_mulVec, eI_eF] }`. Establish `hL : ψ B y = LinearMap.toMatrix' L`.

Use extensionality with `i i'`. Rewrite using `[LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression. Apply `ext_of_eF B` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[φ_apply_mulVec, hL, LinearMap.toMatrix'_mulVec]`. Conclude with `eF_eI B _`.
-/
theorem φ_ψ_of_comm (y : Matrix (Fin (n * d)) (Fin (n * d)) k)
    (hy : ∀ b : k, φ B (algebraMap k _ b) * y = y * φ B (algebraMap k _ b)) : φ B (ψ B y) = y := by
  have hsm : ∀ (b : k) (v : Fin n → k), b • v = algebraMap k (Matrix (Fin n) (Fin n) k) b *ᵥ v := by
    intro b v
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  let L : (Fin n → k) →ₗ[k] (Fin n → k) :=
    { toFun := fun v => eI B (y *ᵥ eF B v)
      map_add' := fun v v' => by
        simp only [eF_add, Matrix.mulVec_add, eI_add]
      map_smul' := fun b v => by
        simp only [RingHom.id_apply]
        rw [hsm b v, hsm b (eI B (y *ᵥ eF B v)), ← φ_apply_mulVec B _ v, Matrix.mulVec_mulVec, ← hy b,
          ← Matrix.mulVec_mulVec]
        conv_lhs => rw [← eF_eI B (y *ᵥ eF B v), φ_apply_mulVec, eI_eF] }
  have hL : ψ B y = LinearMap.toMatrix' L := by
    ext i i'
    rw [LinearMap.toMatrix'_apply]
    rfl
  apply ext_of_eF B
  intro v
  rw [φ_apply_mulVec, hL, LinearMap.toMatrix'_mulVec]
  exact eF_eI B _

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a` using `fun a => by`. Rewrite using `[← SetLike.mem_coe, coe_Z']`. Both sides reduce to the same expression. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `hx' : ∀ a ∈ Z' B Z, a * x = x * a` using `hx`. Establish `hsc : ∀ b : k, φ B (algebraMap k _ b) * x = x * φ B (algebraMap k _ b)` using `fun b => hx' _ ((mem _).2 ⟨_, Z.algebraMap_mem b, rfl⟩)`. Use `⟨ψ B x, ?_, φ_ψ_of_comm B x hsc⟩` and prove the remaining obligations. Use `show ∀ a ∈ Z, a * ψ B x = ψ B x * a`.

Introduce `z hz`. Apply `φ_inj B` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, φ_ψ_of_comm B x hsc]`. Conclude with `hx' _ ((mem _).2 ⟨z, hz, rfl⟩)`. Introduce and unpack `⟨y, hy, rfl⟩`.

Establish `hy' : ∀ a ∈ Z, a * y = y * a` using `hy`. Use `show ∀ a ∈ Z' B Z, a * φ B y = φ B y * a`. Introduce `a ha`. Take `⟨z, hz, rfl⟩` from `(mem a).1 ha`. Rewrite using `[← map_mul, ← map_mul, hy' z hz]`.
-/
theorem cen (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Bz (Z' B Z) = φ B '' Bz Z := by
  have mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a := fun a => by
    rw [← SetLike.mem_coe, coe_Z']
    rfl
  ext x
  constructor
  · intro hx
    have hx' : ∀ a ∈ Z' B Z, a * x = x * a := hx
    have hsc : ∀ b : k, φ B (algebraMap k _ b) * x = x * φ B (algebraMap k _ b) := fun b =>
      hx' _ ((mem _).2 ⟨_, Z.algebraMap_mem b, rfl⟩)
    refine ⟨ψ B x, ?_, φ_ψ_of_comm B x hsc⟩
    show ∀ a ∈ Z, a * ψ B x = ψ B x * a
    intro z hz
    apply φ_inj B
    rw [map_mul, map_mul, φ_ψ_of_comm B x hsc]
    exact hx' _ ((mem _).2 ⟨z, hz, rfl⟩)
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ a ∈ Z, a * y = y * a := hy
    show ∀ a ∈ Z' B Z, a * φ B y = φ B y * a
    intro a ha
    obtain ⟨z, hz, rfl⟩ := (mem a).1 ha
    rw [← map_mul, ← map_mul, hy' z hz]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg' : ∀ a ∈ Z' B Z, a * g'.val = g'.val * a` using `hg`. Establish `h1 : g'.val ∈ φ B '' Bz Z`. Rewrite using `[← cen]`.

Conclude with `hg`. Establish `h2 : (g'⁻¹).val ∈ φ B '' Bz Z`. Rewrite using `[← cen]`. Use `show ∀ a ∈ Z' B Z, a * (g'⁻¹).val = (g'⁻¹).val * a`. Introduce `a ha`.

Establish `e` using `congrArg (fun m => (g'⁻¹).val * m * (g'⁻¹).val) (hg' a ha)`. Simplify using `only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e`. Conclude with `e.symm`. Take `⟨y, hy, hyg⟩` from `h1`. Take `⟨y', hy', hyg'⟩` from `h2`.

Establish `e1 : y * y' = 1` using `φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.mul_inv])`. Establish `e2 : y' * y = 1` using `φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.inv_mul])`. Conclude with `⟨⟨y, y', e1, e2⟩, hy, hyg⟩`. Introduce and unpack `⟨g, hg, hgg⟩`. Establish `h : g'.val ∈ Bz (Z' B Z)`.

Rewrite using `[cen]`. Conclude with `⟨g.val, hg, hgg⟩`. Conclude with `h`.
-/
theorem gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g' : GL (Fin (n * d)) k) :
    g' ∈ Gz (Z' B Z) ↔ ∃ g ∈ Gz Z, φ B g.val = g'.val := by
  constructor
  · intro hg
    have hg' : ∀ a ∈ Z' B Z, a * g'.val = g'.val * a := hg
    have h1 : g'.val ∈ φ B '' Bz Z := by
      rw [← cen]
      exact hg
    have h2 : (g'⁻¹).val ∈ φ B '' Bz Z := by
      rw [← cen]
      show ∀ a ∈ Z' B Z, a * (g'⁻¹).val = (g'⁻¹).val * a
      intro a ha
      have e := congrArg (fun m => (g'⁻¹).val * m * (g'⁻¹).val) (hg' a ha)
      simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
      exact e.symm
    obtain ⟨y, hy, hyg⟩ := h1
    obtain ⟨y', hy', hyg'⟩ := h2
    have e1 : y * y' = 1 := φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.mul_inv])
    have e2 : y' * y = 1 := φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.inv_mul])
    exact ⟨⟨y, y', e1, e2⟩, hy, hyg⟩
  · rintro ⟨g, hg, hgg⟩
    have h : g'.val ∈ Bz (Z' B Z) := by
      rw [cen]
      exact ⟨g.val, hg, hgg⟩
    exact h

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Take `⟨hc, hr⟩` from `hZ`. Establish `mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a` using `fun a => by`. Rewrite using `[← SetLike.mem_coe, coe_Z']`. Both sides reduce to the same expression. Use `⟨?_, ⟨?_⟩⟩` and prove the remaining obligations.

Introduce `a ha b hb`. Take `⟨z, hz, rfl⟩` from `(mem a).1 ha`. Take `⟨w, hw, rfl⟩` from `(mem b).1 hb`. Rewrite using `[← map_mul, ← map_mul, hc z hz w hw]`. Introduce and unpack `⟨x, hx⟩ ⟨m, hm⟩`.

Take `⟨z, hz, rfl⟩` from `(mem x).1 hx`. Establish `hzm : (⟨z, hz⟩ : Z) ^ m = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `φ_inj B` to reduce the goal to its premises. Use `congrArg Subtype.val hm` as an intermediate fact.

Simplify `this` using `[map_pow]`. Establish `h0` using `hr.eq_zero _ ⟨m, hzm⟩`. Establish `hz0 : z = 0` using `congrArg Subtype.val h0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hz0]`.
-/
theorem cr (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : CR (Z' B Z) := by
  obtain ⟨hc, hr⟩ := hZ
  have mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a := fun a => by
    rw [← SetLike.mem_coe, coe_Z']
    rfl
  refine ⟨?_, ⟨?_⟩⟩
  · intro a ha b hb
    obtain ⟨z, hz, rfl⟩ := (mem a).1 ha
    obtain ⟨w, hw, rfl⟩ := (mem b).1 hb
    rw [← map_mul, ← map_mul, hc z hz w hw]
  · rintro ⟨x, hx⟩ ⟨m, hm⟩
    obtain ⟨z, hz, rfl⟩ := (mem x).1 hx
    have hzm : (⟨z, hz⟩ : Z) ^ m = 0 := by
      apply Subtype.ext
      apply φ_inj B
      have := congrArg Subtype.val hm
      simpa [map_pow] using this
    have h0 := hr.eq_zero _ ⟨m, hzm⟩
    have hz0 : z = 0 := congrArg Subtype.val h0
    apply Subtype.ext
    simp [hz0]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Introduce `a` and use `⟨φ B (algebraMap k _ a), ⟨_, Z.algebraMap_mem a, rfl⟩, by rw [← map_pow, ← map_pow, φ_scal]⟩`.
-/
theorem roots (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : HasRoots (Z' B Z) (p ^ c) := fun a =>
  ⟨φ B (algebraMap k _ a), ⟨_, Z.algebraMap_mem a, rfl⟩, by rw [← map_pow, ← map_pow, φ_scal]⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [TopologicalSpace k] in
/- English proof (translation)
Establish `h` using `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hx`. Establish `h2 : x.charpoly = X ^ Fintype.card (Fin n)` using `sub_eq_zero.1 h.eq_zero`. Establish `h3` using `Matrix.aeval_self_charpoly x`. Rewrite `h3` using `[h2, map_pow, aeval_X, Fintype.card_fin]`. Conclude with `h3`.
-/
theorem pow_card_eq_zero (x : Matrix (Fin n) (Fin n) k) (hx : IsNilpotent x) : x ^ n = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hx
  have h2 : x.charpoly = X ^ Fintype.card (Fin n) := sub_eq_zero.1 h.eq_zero
  have h3 := Matrix.aeval_self_charpoly x
  rw [h2, map_pow, aeval_X, Fintype.card_fin] at h3
  exact h3

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Introduce `y hy hnil`. Rewrite `hy` using `[cen]`. Take `⟨x, hx, rfl⟩` from `hy`. Establish `hxn : IsNilpotent x`. Take `⟨m, hm⟩` from `hnil`.

Conclude with `⟨m, φ_inj B (by rw [map_pow, hm, map_zero])⟩`. Rewrite using `[← map_pow, pow_eq_zero_of_le hn (pow_card_eq_zero x hxn), map_zero]`.
-/
theorem nil (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hn : n ≤ p ^ c) : NilBound (Z' B Z) (p ^ c) := by
  intro y hy hnil
  rw [cen] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxn : IsNilpotent x := by
    obtain ⟨m, hm⟩ := hnil
    exact ⟨m, φ_inj B (by rw [map_pow, hm, map_zero])⟩
  rw [← map_pow, pow_eq_zero_of_le hn (pow_card_eq_zero x hxn), map_zero]

end PositivityTheory.RgUd.TP.Desc.Restr.PphiC
