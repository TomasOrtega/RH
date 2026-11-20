import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

/- English proof (translation)
Establish `hat : At (evFin F v) (GlobalTheory.LatVac.liftV v b • (1 : AE F E))`. Introduce `u hu`. Rewrite using `[smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v b u hu, zero_smul]`. Rewrite using `[← ptAt_locW hw h hat]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `complMap h b = toCompl h (compFin F E v (GlobalTheory.LatVac.liftV v b • (1 : AE F E)))`. Rewrite using `[GlobalTheory.ThK.compFin_smul, map_one, GlobalTheory.LatVac.evFin_liftV, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', toCompl_tmul, smul_eq_mul, mul_one, map_one, mul_one]`.
-/
theorem ptAt_complMap (b : Fv F v) : ptAt hw h (complMap h b) = GlobalTheory.LatVac.liftV v b • (1 : AE F E) := by
  have hat : At (evFin F v) (GlobalTheory.LatVac.liftV v b • (1 : AE F E)) := by
    intro u hu
    rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v b u hu, zero_smul]
  rw [← ptAt_locW hw h hat]
  congr 1
  change complMap h b = toCompl h (compFin F E v (GlobalTheory.LatVac.liftV v b • (1 : AE F E)))
  rw [GlobalTheory.ThK.compFin_smul, map_one, GlobalTheory.LatVac.evFin_liftV, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    toCompl_tmul, smul_eq_mul, mul_one, map_one, mul_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] e))) = _`. Rewrite using `[GlobalTheory.ThK.compFin_smul, GlobalTheory.AdelicU.Supp.compFin_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, toCompl_tmul]`.
-/
theorem locW_smul_inclR (a : AF F) (e : E) :
    locW h (a • inclR (F := F) (AF F) e) = complMap h (evFin F v a) * algebraMap E _ e := by
  change toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] e))) = _
  rw [GlobalTheory.ThK.compFin_smul, GlobalTheory.AdelicU.Supp.compFin_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, toCompl_tmul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem mul_vecMulVec_mul {R : Type} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin m) R) (N : Matrix (Fin k) (Fin k) R)
    (p : Fin m → R) (q : Fin k → R) : M * Matrix.vecMulVec p q * Nᵀ = Matrix.vecMulVec (M *ᵥ p) (N *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem mul_transpose_mul_eq_sum {R : Type} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin k) (Fin k) R) (x : Matrix (Fin k) (Fin m) R) :
    A * xᵀ * Bᵀ = ∑ i, ∑ j, x j i • Matrix.vecMulVec (Aᵀ i) (Bᵀ j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

/- English proof (translation)
Take `⟨y, rfl⟩` from `InertChart.toCompl_surjective h t`. Establish `hy` using `(InertChart.mem_intLoc_iff hw h y).2 ht`. Use `intLoc_induction (p := fun y => ∀ γ ∈ latAtV X Y v, ptAt hw h (toCompl h y) • γ ∈ latAtV X Y v) ?_ ?_ ?_ ?_ hy γ hγ` and prove the remaining obligations. Introduce `a ha o γ hγ`. Rewrite using `[toCompl_tmul, mul_comm, ← inclR_mul_ptAt, ptAt_complMap]`.

Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a', ha', hv, x, hx, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * a', ?_, ?_, (o • x), X.L.smul_mem o hx, y, hy, ?_⟩` and prove the remaining obligations. Introduce `u hu`.

Rewrite using `[smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]`. Rewrite using `[map_mul, GlobalTheory.LatVac.evFin_liftV]`. Conclude with `mul_mem ha hv`. Use extensionality with `k l`. Simplify using `only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]`.

Rewrite using `[show algebraMap (𝓞 E) E o = (o : E) from rfl]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`. Introduce `γ hγ`. Rewrite using `[map_zero, map_zero, zero_smul]`.

Conclude with `zero_mem _`. Introduce `y z hy hz γ hγ`. Rewrite using `[map_add, map_add, add_smul]`. Conclude with `add_mem (hy γ hγ) (hz γ hγ)`. Introduce `y hy γ hγ`.

Rewrite using `[map_neg, map_neg, neg_smul]`. Conclude with `neg_mem (hy γ hγ)`.
-/
theorem smul_mem_latAtV {t : w.adicCompletion E} (ht : t ∈ Formalism.UG.Ov E w) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X Y v) : ptAt hw h t • γ ∈ latAtV X Y v := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective h t
  have hy := (InertChart.mem_intLoc_iff hw h y).2 ht
  refine intLoc_induction (p := fun y => ∀ γ ∈ latAtV X Y v, ptAt hw h (toCompl h y) • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy γ hγ
  · intro a ha o γ hγ
    rw [toCompl_tmul, mul_comm, ← inclR_mul_ptAt, ptAt_complMap]
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * a', ?_, ?_, (o • x), X.L.smul_mem o hx, y, hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem ha hv
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [show algebraMap (𝓞 E) E o = (o : E) from rfl]
        ring
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro γ hγ; rw [map_zero, map_zero, zero_smul]; exact zero_mem _
  · intro y z hy hz γ hγ; rw [map_add, map_add, add_smul]; exact add_mem (hy γ hγ) (hz γ hγ)
  · intro y hy γ hγ; rw [map_neg, map_neg, neg_smul]; exact neg_mem (hy γ hγ)

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

/- English proof (translation)
Use `inclR_mul_ptAt hw h e 1` as an intermediate fact. Rewrite `this` using `[mul_one, ← (complMap h).map_one, ptAt_complMap, mul_smul_comm, mul_one]`. Conclude with `this.symm`.
-/
theorem ptAt_algebraMap (e : E) :
    ptAt hw h (algebraMap E (w.adicCompletion E) e) = GlobalTheory.LatVac.liftV v 1 • inclR (F := F) (AF F) e := by
  have := inclR_mul_ptAt hw h e 1
  rw [mul_one, ← (complMap h).map_one, ptAt_complMap, mul_smul_comm, mul_one] at this
  exact this.symm

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem p hp`. Take `⟨x, hx, rfl⟩` from `hp`. Proceed by induction on `hq using Submodule.span_induction with`. Consider the case `mem q hq`.

Take `⟨y, hy, rfl⟩` from `hq`. Use `AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1, ?_, x, hx, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatVac.evFin_liftV]`. Conclude with `one_mem _`. Use extensionality with `k l`.

Simplify using `only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, ← map_mul, ptAt_algebraMap]`. Consider the case `zero`. Use `zero_mem (latAtV X Y v) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `[Matrix.vecMulVec_apply]`.

Consider the case `add q q' _ _ h1 h2`. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `[Matrix.vecMulVec_apply, mul_add]`. Consider the case `smul t q _ h1`.

Use `smul_mem_latAtV hw h X Y t.2 h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[Subring.smul_def, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `zero_mem (latAtV X Y v) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `[Matrix.vecMulVec_apply]`.

Consider the case `add p p' _ _ h1 h2`. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `[Matrix.vecMulVec_apply, add_mul]`. Consider the case `smul t p _ h1`.

Use `smul_mem_latAtV hw h X Y t.2 h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[Subring.smul_def, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_mem {p : Fin n → w.adicCompletion E} (hp : p ∈ latAt w X.L) {q : Fin d → w.adicCompletion E}
    (hq : q ∈ latAt w Y.L) : (Matrix.vecMulVec p q).map (ptAt hw h) ∈ latAtV X Y v := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨x, hx, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨y, hy, rfl⟩ := hq
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1, ?_, x, hx, y, hy, ?_⟩
      · rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, ← map_mul, ptAt_algebraMap]
    | zero =>
      convert zero_mem (latAtV X Y v) using 1
      ext k l; simp [Matrix.vecMulVec_apply]
    | add q q' _ _ h1 h2 =>
      convert add_mem h1 h2 using 1
      ext k l; simp [Matrix.vecMulVec_apply, mul_add]
    | smul t q _ h1 =>
      convert smul_mem_latAtV hw h X Y t.2 h1 using 1
      ext k l
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
      congr 1
      rw [Subring.smul_def, smul_eq_mul]
      ring
  | zero =>
    convert zero_mem (latAtV X Y v) using 1
    ext k l; simp [Matrix.vecMulVec_apply]
  | add p p' _ _ h1 h2 =>
    convert add_mem h1 h2 using 1
    ext k l; simp [Matrix.vecMulVec_apply, add_mul]
  | smul t p _ h1 =>
    convert smul_mem_latAtV hw h X Y t.2 h1 using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
    congr 1
    rw [Subring.smul_def, smul_eq_mul]
    ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

open GlobalTheory.InertCoord in

/- English proof (translation)
Introduce `F E _ _ _ _ _ v w hw h n d X Y A Bm hA hB x`. Establish `col : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)}, IsFrameAt w L C → ∀ i, (C : Matrix (Fin m) (Fin m) (w.adicCompletion E))ᵀ i ∈ latAt w L`. Introduce `m L C hC i`. Use `(hC (Pi.single i 1)).1 fun k => by` as an intermediate fact. Distinguish the cases in `e : k = i`.

Substitute `e` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne e]`. Conclude with `zero_mem _`.

Rewrite `this` using `[Matrix.mulVec_single_one]`. Then use the resulting hypothesis. Establish `inv : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)}, IsFrameAt w L C → ∀ z ∈ L, ∀ k, ((↑C⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ fun i => algebraMap E (w.adicCompletion E) (z i)) k ∈ Formalism.UG.Ov E w`. Introduce `m L C hC z hz`. Use `(hC _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `Submodule.subset_span ⟨z, hz, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite using `[kap_apply, mul_transpose_mul_eq_sum]`. Express the relevant statement in the definitionally equal form `_ ∈ (latAtV X Y v).comap (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom)`.

Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x j i • Matrix.vecMulVec _ _).map (ptAt hw h) ∈ latAtV X Y v`. Use `smul_mem_latAtV hw h X Y (hx j i) (vecMulVec_mem hw h X Y (col hA i) (col hB j)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`.

Introduce `hk i j`. Set `Ψ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (w.adicCompletion E)` to `fun γ => (↑A⁻¹ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * AddMonoidHom.mapMatrix (locW h).toAddMonoidHom γ * (↑Bm⁻¹ : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ`. Establish `hΨ : ∀ γ ∈ latAtV X Y v, ∀ k l, Ψ γ k l ∈ Formalism.UG.Ov E w`. Introduce `γ hγ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨a, -, ha, p, hp, q, hq, rfl⟩` from `hz`. Establish `e1 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (a • incM F (Matrix.vecMulVec p q)) = complMap h (evFin F v a) • Matrix.vecMulVec (fun i => algebraMap E (w.adicCompletion E) (p i)) (fun i => algebraMap E (w.adicCompletion E) (q i))`. Use `Matrix.ext fun k l => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `locW h (a • inclR (F := F) (AF F) (p k * q l)) = _`.

Rewrite using `[locW_smul_inclR, map_mul]`. Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]`. Introduce `k l`. Simplify using `only [Ψ, e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]`. Conclude with `mul_mem (complMap_mem h ha) (mul_mem (inv hA p hp k) (inv hB q hq l))`.

Consider the case `zero => intro k l`. Simplify using `[Ψ]`. Consider the case `add x y _ _ hx hy`. Introduce `k l`. Simplify using `only [Ψ, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]`.

Conclude with `add_mem (hx k l) (hy k l)`. Consider the case `neg x _ hx`. Introduce `k l`. Simplify using `only [Ψ, map_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]`. Conclude with `neg_mem (hx k l)`.

Establish `e : Ψ (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = xᵀ`. Establish `e2 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ`. Use `Matrix.ext fun k l => ?_` and prove the remaining obligations. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, kap_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, locW_ptAt]`. Simplify using `only [Ψ, e2]`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Use `hΨ _ hk j i` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem kap_mem_latAtV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ v w hw h n d X Y A Bm hA hB x
  have col : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ i, (C : Matrix (Fin m) (Fin m) (w.adicCompletion E))ᵀ i ∈ latAt w L := by
    intro m L C hC i
    have := (hC (Pi.single i 1)).1 fun k => by
      by_cases e : k = i
      · subst e; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _
    rwa [Matrix.mulVec_single_one] at this
  have inv : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ z ∈ L, ∀ k, ((↑C⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ
        fun i => algebraMap E (w.adicCompletion E) (z i)) k ∈ Formalism.UG.Ov E w := by
    intro m L C hC z hz
    refine (hC _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  constructor
  · intro hx
    rw [kap_apply, mul_transpose_mul_eq_sum]
    change _ ∈ (latAtV X Y v).comap (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom)
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    change (x j i • Matrix.vecMulVec _ _).map (ptAt hw h) ∈ latAtV X Y v
    convert smul_mem_latAtV hw h X Y (hx j i) (vecMulVec_mem hw h X Y (col hA i) (col hB j)) using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  · intro hk i j
    let Ψ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (w.adicCompletion E) := fun γ =>
      (↑A⁻¹ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * AddMonoidHom.mapMatrix (locW h).toAddMonoidHom γ *
        (↑Bm⁻¹ : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ
    have hΨ : ∀ γ ∈ latAtV X Y v, ∀ k l, Ψ γ k l ∈ Formalism.UG.Ov E w := by
      intro γ hγ
      induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, ha, p, hp, q, hq, rfl⟩ := hz
        have e1 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (a • incM F (Matrix.vecMulVec p q)) =
            complMap h (evFin F v a) • Matrix.vecMulVec (fun i => algebraMap E (w.adicCompletion E) (p i))
              (fun i => algebraMap E (w.adicCompletion E) (q i)) := by
          refine Matrix.ext fun k l => ?_
          change locW h (a • inclR (F := F) (AF F) (p k * q l)) = _
          rw [locW_smul_inclR, map_mul]
          simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
        intro k l
        simp only [Ψ, e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, Matrix.smul_apply,
          Matrix.vecMulVec_apply, smul_eq_mul]
        exact mul_mem (complMap_mem h ha) (mul_mem (inv hA p hp k) (inv hB q hq l))
      | zero => intro k l; simp [Ψ]
      | add x y _ _ hx hy =>
        intro k l
        simp only [Ψ, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hx k l) (hy k l)
      | neg x _ hx =>
        intro k l
        simp only [Ψ, map_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
        exact neg_mem (hx k l)
    have e : Ψ (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = xᵀ := by
      have e2 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
          (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
        refine Matrix.ext fun k l => ?_
        simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, kap_apply, RingHom.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, locW_ptAt]
      simp only [Ψ, e2]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have := hΨ _ hk j i
    rw [e] at this
    exact this

end GlobalTheory.InertLat
