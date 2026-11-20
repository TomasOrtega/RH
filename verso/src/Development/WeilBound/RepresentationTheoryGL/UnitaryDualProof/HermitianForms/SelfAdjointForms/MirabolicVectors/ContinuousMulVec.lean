import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDetStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.mir

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def gLat {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) :=
  A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).toAddMonoidHom

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem mulVec_inv_mulVec {n : ℕ} (g : GL (Fin n) k) (x : Fin n → k) :
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem mulVec_mulVec_inv {n : ℕ} (g : GL (Fin n) k) (x : Fin n → k) :
    (g : Matrix (Fin n) (Fin n) k) *ᵥ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Use extensionality with `x`. Use `show ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) ∈ A ↔ x ∈ A`. Rewrite using `[mulVec_inv_mulVec]`.
-/
theorem comap_gLat {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) :
    (gLat g A).comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom = A := by
  ext x
  show ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) ∈ A ↔ x ∈ A
  rw [mulVec_inv_mulVec]

/- English proof (translation)
The claim follows from `continuous_const.matrix_mulVec continuous_id`.
-/
theorem continuous_mulVec' {n : ℕ} (M : Matrix (Fin n) (Fin n) k) : Continuous fun x : Fin n → k => M *ᵥ x :=
  continuous_const.matrix_mulVec continuous_id

/- English proof (translation)
Establish `e : ((gLat g A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = (fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) '' (A : Set (Fin (m + 1) → k))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, mulVec_mulVec_inv g x⟩`.

Introduce and unpack `⟨y, hy, rfl⟩ show ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ _ ∈ A`. Rewrite using `[mulVec_inv_mulVec]`. Conclude with `hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `hA.1.image (continuous_mulVec' _)`. Conclude with `hA.2.preimage (continuous_mulVec' _)`.
-/
theorem isLat_gLat {m : ℕ} (g : GL (Fin (m + 1)) k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    IsLat (gLat g A) := by
  have e : ((gLat g A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) '' (A : Set (Fin (m + 1) → k)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, mulVec_mulVec_inv g x⟩
    · rintro ⟨y, hy, rfl⟩
      show ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ _ ∈ A
      rw [mulVec_inv_mulVec]; exact hy
  refine ⟨?_, ?_⟩
  · rw [e]; exact hA.1.image (continuous_mulVec' _)
  · exact hA.2.preimage (continuous_mulVec' _)

/- English proof (translation)
Use `⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩` and prove the remaining obligations. Establish `e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => p.1 + p.2) '' ((A : Set _) ×ˢ (B : Set _))`. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_sup]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, z, hz, rfl⟩`. Conclude with `⟨(y, z), ⟨hy, hz⟩, rfl⟩`. Introduce and unpack `⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩`. Conclude with `⟨y, hy, z, hz, rfl⟩`. Rewrite using `[e]`.

Conclude with `(hA.1.prod hB.1).image continuous_add`.
-/
theorem isLat_sup {m : ℕ} {A B : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => p.1 + p.2) '' ((A : Set _) ×ˢ (B : Set _)) := by
    ext x
    rw [SetLike.mem_coe, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨(y, z), ⟨hy, hz⟩, rfl⟩
    · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
      exact ⟨y, hy, z, hz, rfl⟩
  rw [e]
  exact (hA.1.prod hB.1).image continuous_add

/- English proof (translation)
Take `⟨q, hq, hav⟩` from `avg_spec ψ h π hψ hπ ξ A hA v`. Rewrite using `[hav]`. Use `set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v with hf`. Establish `inv : ∀ (r : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)), AvgData ψ h π ξ A v r → ∀ x, ∀ d ∈ r.1, f (x + d) = f x`. Introduce `r hr x d hd`.

Simplify using `only [hf]`. Rewrite using `[colEl_add, map_mul, Module.End.mul_apply, hr.2.2.1 d hd, dotProduct_add, AddChar.map_add_eq_mul, hr.2.2.2.1 d hd, mul_one]`. Establish `hpq : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = (p.2.card : ℂ) • ∑ s ∈ q.2, f s`. Rewrite using `[Finset.sum_congr rfl (fun t ht => sum_translate_transversal A q.1 q.2 hq.2.2.2.2.1 hq.2.2.2.2.2 f (inv q hq) t (hp.2.2.2.2.1 t ht)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `hqp : ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s) = (q.2.card : ℂ) • ∑ t ∈ p.2, f t`.

Rewrite using `[Finset.sum_congr rfl (fun s hs => sum_translate_transversal A p.1 p.2 hp.2.2.2.2.1 hp.2.2.2.2.2 f (inv p hp) s (hq.2.2.2.2.1 s hs)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `hcomm : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [add_comm]` and prove the remaining obligations. Take `⟨t₀, ⟨ht₀, _⟩, _⟩` from `hp.2.2.2.2.2 0 A.zero_mem`.

Take `⟨s₀, ⟨hs₀, _⟩, _⟩` from `hq.2.2.2.2.2 0 A.zero_mem`. Establish `hcp : (p.2.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht₀)`. Establish `hcq : (q.2.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs₀)`. Establish `key : (p.2.card : ℂ) • ∑ s ∈ q.2, f s = (q.2.card : ℂ) • ∑ t ∈ p.2, f t`. Rewrite using `[← hpq, ← hqp, hcomm]`.

Establish `key2` using `congrArg (fun x => ((p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹) • x) key`. Simplify using `only [smul_smul] at key2`. Rewrite `key2` using `[show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (p.2.card : ℂ) = (q.2.card : ℂ)⁻¹ by field_simp, show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (q.2.card : ℂ) = (p.2.card : ℂ)⁻¹ by field_simp]`. Conclude with `key2`.
-/
theorem avg_eq_of_data (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) (p) (hp : AvgData ψ h π ξ A v p) :
    avg ψ h π ξ A v =
      ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  obtain ⟨q, hq, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  rw [hav]
  set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
    with hf
  have inv : ∀ (r : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)), AvgData ψ h π ξ A v r →
      ∀ x, ∀ d ∈ r.1, f (x + d) = f x := by
    intro r hr x d hd
    simp only [hf]
    rw [colEl_add, map_mul, Module.End.mul_apply, hr.2.2.1 d hd, dotProduct_add, AddChar.map_add_eq_mul,
      hr.2.2.2.1 d hd, mul_one]

  have hpq : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = (p.2.card : ℂ) • ∑ s ∈ q.2, f s := by
    rw [Finset.sum_congr rfl (fun t ht => sum_translate_transversal A q.1 q.2 hq.2.2.2.2.1 hq.2.2.2.2.2 f
      (inv q hq) t (hp.2.2.2.2.1 t ht)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  have hqp : ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s) = (q.2.card : ℂ) • ∑ t ∈ p.2, f t := by
    rw [Finset.sum_congr rfl (fun s hs => sum_translate_transversal A p.1 p.2 hp.2.2.2.2.1 hp.2.2.2.2.2 f
      (inv p hp) s (hq.2.2.2.2.1 s hs)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  have hcomm : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [add_comm]
  obtain ⟨t₀, ⟨ht₀, _⟩, _⟩ := hp.2.2.2.2.2 0 A.zero_mem
  obtain ⟨s₀, ⟨hs₀, _⟩, _⟩ := hq.2.2.2.2.2 0 A.zero_mem
  have hcp : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht₀)
  have hcq : (q.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs₀)
  have key : (p.2.card : ℂ) • ∑ s ∈ q.2, f s = (q.2.card : ℂ) • ∑ t ∈ p.2, f t := by
    rw [← hpq, ← hqp, hcomm]
  have key2 := congrArg (fun x => ((p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹) • x) key
  simp only [smul_smul] at key2
  rw [show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (p.2.card : ℂ) = (q.2.card : ℂ)⁻¹ by field_simp,
    show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (q.2.card : ℂ) = (p.2.card : ℂ)⁻¹ by field_simp] at key2
  exact key2

/- English proof (translation)
Use `set P := blkAt k (m + 1) N (by omega) g with hP`. Establish `hconj : ∀ x, π P (π (colEl k m N h x) v) = π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π P v)`. Introduce `x`. Establish `e : P * colEl k m N h x = colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) * P`. Rewrite using `[← blkAt_conj_colEl h g x, ← hP]`.

Use `group`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]`. Take `⟨p, hp, hav⟩` from `avg_spec ψ h π hψ hπ ξ A hA v`. Take `⟨hMA, hMo, hMfix, hMchar, hT, hu⟩` from `hp`. Set `gv : (Fin (m + 1) → k) → (Fin (m + 1) → k)` to `fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x`.

Establish `ginj : Function.Injective gv` using `fun x y e => by`. Use `congrArg (fun z => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ z) e` as an intermediate fact. Simplify `this` using `[gv, mulVec_inv_mulVec]`. Set `p' : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)` to `(gLat g p.1, p.2.image gv)`. Establish `hp' : AvgData ψ h π η (gLat g A) (π P v) p'`.

Use `⟨fun x hx => hMA hx, hMo.preimage (continuous_mulVec' _), fun a ha => ?_, fun a ha => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `hconj (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)`. Rewrite `e` using `[mulVec_mulVec_inv, hMfix (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha]`. Conclude with `e.symm`. Establish `e` using `hη (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)`.

Rewrite `e` using `[mulVec_mulVec_inv]`. Rewrite using `[e]`. Conclude with `hMchar (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha`. Introduce `t ht`. Take `⟨t', ht', rfl⟩` from `Finset.mem_image.1 ht`.

Use `show _ *ᵥ (gv t') ∈ A`. Simplify using `only [gv, mulVec_inv_mulVec]`. Conclude with `hT t' ht'`. Introduce `a ha`. Take `⟨t, ⟨htT, hta⟩, hun⟩` from `hu _ ha`.

Use `⟨gv t, ⟨Finset.mem_image_of_mem _ htT, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show _ *ᵥ (a - gv t) ∈ p.1`. Rewrite using `[Matrix.mulVec_sub]`. Simplify using `only [gv, mulVec_inv_mulVec]`. Conclude with `hta`.

Introduce and unpack `t' ⟨ht', ht'a⟩`. Take `⟨t1, ht1, rfl⟩` from `Finset.mem_image.1 ht'`. Use `congr 1`. Use `hun t1 ⟨ht1, ?_⟩` and prove the remaining obligations. Establish `: _ *ᵥ (a - gv t1) ∈ p.1` using `ht'a`.

Rewrite `this` using `[Matrix.mulVec_sub, mulVec_inv_mulVec]`. Then use the resulting hypothesis. Rewrite using `[avg_eq_of_data ψ h π hψ hπ η (isLat_gLat g hA) _ p' hp', hav, map_smul, map_sum, Finset.card_image_of_injective _ ginj, Finset.sum_image (fun x _ y _ e => ginj e)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hconj, hη]`.
-/
theorem avg_conj (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hψ : Continuous ψ) (hπ : IsSmooth π) (g : GL (Fin (m + 1)) k)
    (ξ η : Fin (m + 1) → k) (hη : ∀ x, η ⬝ᵥ ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = ξ ⬝ᵥ x)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    π (blkAt k (m + 1) N (by omega) g) (avg ψ h π ξ A v) =
      avg ψ h π η (gLat g A) (π (blkAt k (m + 1) N (by omega) g) v) := by
  classical
  set P := blkAt k (m + 1) N (by omega) g with hP
  have hconj : ∀ x, π P (π (colEl k m N h x) v) =
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π P v) := by
    intro x
    have e : P * colEl k m N h x = colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) * P := by
      rw [← blkAt_conj_colEl h g x, ← hP]; group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  obtain ⟨p, hp, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  obtain ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩ := hp
  let gv : (Fin (m + 1) → k) → (Fin (m + 1) → k) := fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x
  have ginj : Function.Injective gv := fun x y e => by
    have := congrArg (fun z => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ z) e
    simpa [gv, mulVec_inv_mulVec] using this
  let p' : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k) := (gLat g p.1, p.2.image gv)
  have hp' : AvgData ψ h π η (gLat g A) (π P v) p' := by
    refine ⟨fun x hx => hMA hx, hMo.preimage (continuous_mulVec' _), fun a ha => ?_, fun a ha => ?_, ?_, ?_⟩
    · have e := hconj (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)
      rw [mulVec_mulVec_inv, hMfix (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha] at e
      exact e.symm
    · have e := hη (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)
      rw [mulVec_mulVec_inv] at e
      rw [e]; exact hMchar (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
      show _ *ᵥ (gv t') ∈ A
      simp only [gv, mulVec_inv_mulVec]; exact hT t' ht'
    · intro a ha
      obtain ⟨t, ⟨htT, hta⟩, hun⟩ := hu _ ha
      refine ⟨gv t, ⟨Finset.mem_image_of_mem _ htT, ?_⟩, ?_⟩
      · show _ *ᵥ (a - gv t) ∈ p.1
        rw [Matrix.mulVec_sub]; simp only [gv, mulVec_inv_mulVec]; exact hta
      · rintro t' ⟨ht', ht'a⟩
        obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 ht'
        congr 1
        refine hun t1 ⟨ht1, ?_⟩
        have : _ *ᵥ (a - gv t1) ∈ p.1 := ht'a
        rwa [Matrix.mulVec_sub, mulVec_inv_mulVec] at this
  rw [avg_eq_of_data ψ h π hψ hπ η (isLat_gLat g hA) _ p' hp', hav, map_smul, map_sum,
    Finset.card_image_of_injective _ ginj, Finset.sum_image (fun x _ y _ e => ginj e)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hconj, hη]

/- English proof (translation)
Introduce `p hp v w`. Use `set P := blkAt k (m + 1) N (by omega) p with hPdef`. Take `⟨A₁, hA₁, h01, hA₁'⟩` from `hD (π P v) (π P w)`. Take `⟨A₂, hA₂, h02, hA₂'⟩` from `hD v w`. Use `set A' := A₂ ⊔ A₁.comap (Matrix.mulVecLin (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom with hA'`.

Establish `hA'l : IsLat A'`. Use `isLat_sup hA₂ ?_` and prove the remaining obligations. Use `isLat_gLat p⁻¹ hA₁` as an intermediate fact. Simplify `this` using `[gLat]`. Use `set A := gLat p A' with hAdef`.

Establish `hAl : IsLat A` using `isLat_gLat p hA'l`. Establish `h1A : A₁ ≤ A`. Introduce `x hx`. Use `show _ *ᵥ x ∈ A'`. Use `AddSubgroup.mem_sup_right ?_` and prove the remaining obligations.

Use `show (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ (_ *ᵥ x) ∈ A₁`. Rewrite using `[mulVec_mulVec_inv]`. Conclude with `hx`. Establish `h2A' : A₂ ≤ A'` using `le_sup_left`. Establish `hη : ∀ x, xi0 k m ⬝ᵥ ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = xi0 k m ⬝ᵥ x`.

Introduce `x`. Rewrite using `[Matrix.dotProduct_mulVec]`. Conclude with `congrArg (· ⬝ᵥ x) hp`. Establish `e1` using `hA₁' A hAl h1A`. Establish `e2` using `hA₂' A' hA'l h2A'`.

Establish `hconj` using `avg_conj ψ h π hB.cont hB.smooth p (xi0 k m) (xi0 k m) hη hA'l v`. Rewrite `hconj` using `[← hPdef]`. Establish `hBP : ∀ a b, B (π P a) (π P b) = ((nabs k (Matrix.GeneralLinearGroup.det p) ^ s : ℝ) : ℂ) * B a b`. Introduce `a b`. Establish `e` using `hB.mir (glEmb k (m + 1) p) (glEmb_mem_Mir k (m + 1) p) a b`.

Rewrite `e` using `[blkAt_glEmb h p, det_glEmb]`. Conclude with `e`. Establish `hidx : ((A₀.relIndex A : ℕ) : ℝ) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ) * ((A₀.relIndex A' : ℕ) : ℝ)`. Use `GlobalTheory.T.relIndex_lattice_eq_haar_det k (m + 1) p A₀ A hAl.1 hA₀.2 (h01.trans h1A) (by rw [comap_gLat]; exact h02.trans h2A')` as an intermediate fact. Rewrite `this` using `[comap_gLat]`. Then use the resulting hypothesis.

Rewrite using `[e1, ← hconj, hBP, e2]`. Establish `hn : nabs k (Matrix.GeneralLinearGroup.det p) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ)` using `rfl`. Establish `hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det p)`. Rewrite using `[hn]`. Conclude with `NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos`.

Establish `hidxC : ((A₀.relIndex A : ℕ) : ℂ) = ((nabs k (Matrix.GeneralLinearGroup.det p) : ℝ) : ℂ) * ((A₀.relIndex A' : ℕ) : ℂ)`. Rewrite using `[hn]`. Conclude with `hidx` after adjusting the coercions. Rewrite using `[hidxC, Real.rpow_add hpos, Real.rpow_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_mir {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : Lv ψ h π s B)
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : MirEq π m (by omega) (s + 1) B' := by
  intro p hp v w
  set P := blkAt k (m + 1) N (by omega) p with hPdef
  obtain ⟨A₁, hA₁, h01, hA₁'⟩ := hD (π P v) (π P w)
  obtain ⟨A₂, hA₂, h02, hA₂'⟩ := hD v w

  set A' := A₂ ⊔ A₁.comap (Matrix.mulVecLin (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom with hA'
  have hA'l : IsLat A' := by
    refine isLat_sup hA₂ ?_
    have := isLat_gLat p⁻¹ hA₁
    simpa [gLat] using this
  set A := gLat p A' with hAdef
  have hAl : IsLat A := isLat_gLat p hA'l
  have h1A : A₁ ≤ A := by
    intro x hx
    show _ *ᵥ x ∈ A'
    refine AddSubgroup.mem_sup_right ?_
    show (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ (_ *ᵥ x) ∈ A₁
    rw [mulVec_mulVec_inv]; exact hx
  have h2A' : A₂ ≤ A' := le_sup_left
  have hη : ∀ x, xi0 k m ⬝ᵥ ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = xi0 k m ⬝ᵥ x := by
    intro x
    rw [Matrix.dotProduct_mulVec]
    exact congrArg (· ⬝ᵥ x) hp
  have e1 := hA₁' A hAl h1A
  have e2 := hA₂' A' hA'l h2A'
  have hconj := avg_conj ψ h π hB.cont hB.smooth p (xi0 k m) (xi0 k m) hη hA'l v
  rw [← hPdef] at hconj

  have hBP : ∀ a b, B (π P a) (π P b) = ((nabs k (Matrix.GeneralLinearGroup.det p) ^ s : ℝ) : ℂ) * B a b := by
    intro a b
    have e := hB.mir (glEmb k (m + 1) p) (glEmb_mem_Mir k (m + 1) p) a b
    rw [blkAt_glEmb h p, det_glEmb] at e
    exact e

  have hidx : ((A₀.relIndex A : ℕ) : ℝ) =
      (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ) * ((A₀.relIndex A' : ℕ) : ℝ) := by
    have := GlobalTheory.T.relIndex_lattice_eq_haar_det k (m + 1) p A₀ A hAl.1 hA₀.2 (h01.trans h1A)
      (by rw [comap_gLat]; exact h02.trans h2A')
    rwa [comap_gLat] at this
  rw [e1, ← hconj, hBP, e2]
  have hn : nabs k (Matrix.GeneralLinearGroup.det p) =
      (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ) := rfl
  have hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det p) := by
    rw [hn]; exact NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos
  have hidxC : ((A₀.relIndex A : ℕ) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det p) : ℝ) : ℂ) * ((A₀.relIndex A' : ℕ) : ℂ) := by
    rw [hn]; exact_mod_cast hidx
  rw [hidxC, Real.rpow_add hpos, Real.rpow_one]
  push_cast
  ring

end PositivityTheory.RgUd.Form.LeviSmoothness.mir
