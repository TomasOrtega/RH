import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Sgl

variable {F : Type} [Field F] [NumberField F] {v : Pl F}

/- English proof (translation)
The claim follows from `evalV_singleFin_self v x`.
-/
theorem ev_sgl (x : Fv F v) : evFin F v (sgl v x) = x := evalV_singleFin_self v x

/- English proof (translation)
Use `Prod.ext (mul_zero _) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a.2 * singleFin v x = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 * x)`. Use `af_ext fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `h : u = v`.

Substitute `h` using the available equality. Rewrite using `[evalV_singleFin_self, evalV_singleFin_self]`. Rewrite using `[evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]`.
-/
theorem mul_sgl (a : AF F) (x : Fv F v) : a * sgl v x = sgl v (evFin F v a * x) := by
  refine Prod.ext (mul_zero _) ?_
  change a.2 * singleFin v x = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 * x)
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

/- English proof (translation)
Use `⟨fun h => ?_, fun h u hu => ?_⟩` and prove the remaining obligations. Use `h (1 - sgl v 1) (by rw [map_sub, map_one, ev_sgl, sub_self])` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this.symm`. Rewrite using `[← h, smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]`.
-/
theorem kd_at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evFin F v) z ↔ sgl v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sgl v 1) (by rw [map_sub, map_one, ev_sgl, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]`.
-/
theorem at_sgl_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (x : Fv F v) (z : M) : At (evFin F v) (sgl v x • z) :=
  fun u hu => by rw [smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

/- English proof (translation)
Rewrite using `[← kd_at_iff.1 h, smul_eq_mul, mul_comm, mul_sgl, mul_one, ev_sgl]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_eq_sgl {z : AF F} (h : At (evFin F v) z) : z = sgl v (evFin F v z) := by
  rw [← kd_at_iff.1 h, smul_eq_mul, mul_comm, mul_sgl, mul_one, ev_sgl]

/- English proof (translation)
Introduce `u hu` and use `by rw [← map_smul, h u hu, map_zero]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_map {M N : Type} [AddCommGroup M] [Module (AF F) M] [AddCommGroup N] [Module (AF F) N] (f : M →ₗ[AF F] N) {z : M}
    (h : At (evFin F v) z) : At (evFin F v) (f z) := fun u hu => by rw [← map_smul, h u hu, map_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_add, h u hu, h' u hu, add_zero]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_add {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z + z') := fun u hu => by rw [smul_add, h u hu, h' u hu, add_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_sub, h u hu, h' u hu, sub_zero]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_sub {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z - z') := fun u hu => by rw [smul_sub, h u hu, h' u hu, sub_zero]

end Sgl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β γ : Type}

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.smul_mul, h u hu, Matrix.zero_mul]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_right [Fintype β] {z : Matrix α β (AE F E)} (h : At (evFin F v) z) (m : Matrix β γ (AE F E)) :
    At (evFin F v) (z * m) := fun u hu => by rw [← Matrix.smul_mul, h u hu, Matrix.zero_mul]

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.mul_smul, h u hu, Matrix.mul_zero]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_left [Fintype β] {z : Matrix β γ (AE F E)} (h : At (evFin F v) z) (m : Matrix α β (AE F E)) :
    At (evFin F v) (m * z) := fun u hu => by rw [← Matrix.mul_smul, h u hu, Matrix.mul_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]`.
-/
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_transpose {z : Matrix α β (AE F E)} (h : At (evFin F v) z) : At (evFin F v) zᵀ :=
  fun u hu => by rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i j u hu => congrFun (congrFun (h u hu) i) j, fun h u hu => Matrix.ext fun i j => h i j u hu⟩`.
-/
theorem kd_at_matrix {z : Matrix α β (AE F E)} : At (evFin F v) z ↔ ∀ i j, At (evFin F v) (z i j) :=
  ⟨fun h i j u hu => congrFun (congrFun (h u hu) i) j, fun h u hu => Matrix.ext fun i j => h i j u hu⟩

def secM (sec : Fv F v × Fv F v → AE F E) (P Q : Matrix α β (Fv F v)) : Matrix α β (AE F E) := Matrix.of fun i j => sec (P i j, Q i j)

namespace IsSec

variable (h : IsSec σ t sec)
include h

/- English proof (translation)
The claim follows from `kd_at_matrix.2 fun _ _ => h.at' _`.
-/
theorem atM (P Q : Matrix α β (Fv F v)) : At (evFin F v) (secM sec P Q) := kd_at_matrix.2 fun _ _ => h.at' _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => h.fst _`.
-/
theorem fstM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW t) = P := Matrix.ext fun _ _ => h.fst _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => h.snd _`.
-/
theorem sndM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW (t.comp σ)) = Q := Matrix.ext fun _ _ => h.snd _

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => sub_eq_zero.1 (h.ext _ (kd_at_matrix.1 ha i j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j))`.
-/
theorem extM {z z' : Matrix α β (AE F E)} (ha : At (evFin F v) (z - z')) (h1 : z.map (piW t) = z'.map (piW t))
    (h2 : z.map (piW (t.comp σ)) = z'.map (piW (t.comp σ))) : z = z' := Matrix.ext fun i j =>
  sub_eq_zero.1 (h.ext _ (kd_at_matrix.1 ha i j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j)
    (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j))

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => (h.conj _).1`.
-/
theorem conj1 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW t) = z.map (piW (t.comp σ)) := Matrix.ext fun _ _ => (h.conj _).1

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => (h.conj _).2`.
-/
theorem conj2 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW (t.comp σ)) = z.map (piW t) := Matrix.ext fun _ _ => (h.conj _).2

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => (h.smul _ _).1`.
-/
theorem smul1 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW t) = evFin F v a • z.map (piW t) :=
  Matrix.ext fun _ _ => (h.smul _ _).1

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => (h.smul _ _).2`.
-/
theorem smul2 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW (t.comp σ)) = evFin F v a • z.map (piW (t.comp σ)) :=
  Matrix.ext fun _ _ => (h.smul _ _).2

variable [Fintype β] [DecidableEq β]

/- English proof (translation)
Establish `k1 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW t) = a` using `fun a b => by`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.fstM]`. Normalize the expressions using the abelian group laws. Establish `k2 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW (t.comp σ)) = b` using `fun a b => by`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.sndM]`.

Normalize the expressions using the abelian group laws. Establish `k3 : ∀ a b a' b' : Matrix β β (Fv F v), a * a' = 1 → b * b' = 1 → (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) = 1` using `fun a b a' b' e1 e2 => by`. Use `h.extM ?_ ?_ ?_` and prove the remaining obligations. Establish `: (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) - 1 = secM sec (a - 1) (b - 1) * (1 + secM sec (a' - 1) (b' - 1)) + secM sec (a' - 1) (b' - 1)` using `by noncomm_ring`. Rewrite using `[this]`.

Conclude with `((h.atM _ _).kd_mul_right _).kd_add (h.atM _ _)`. Rewrite using `[Matrix.map_mul, k1, k1, e1, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Matrix.map_mul, k2, k2, e2, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨⟨1 + secM sec (g₁.1 - 1) (g₂.1 - 1), 1 + secM sec ((g₁⁻¹).1 - 1) ((g₂⁻¹).1 - 1), k3 _ _ _ _ g₁.mul_inv g₂.mul_inv, k3 _ _ _ _ g₁.inv_mul g₂.inv_mul⟩, ?_, k1 _ _, k2 _ _⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk, add_sub_cancel_left]`.

Conclude with `h.atM _ _`.
-/
theorem exists_gl (g₁ g₂ : GL β (Fv F v)) : ∃ g : GL β (AE F E), At (evFin F v) ((g : Matrix β β (AE F E)) - 1) ∧
    (g : Matrix β β (AE F E)).map (piW t) = g₁ ∧ (g : Matrix β β (AE F E)).map (piW (t.comp σ)) = g₂ := by
  have k1 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW t) = a := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.fstM]; abel
  have k2 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW (t.comp σ)) = b := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.sndM]; abel
  have k3 : ∀ a b a' b' : Matrix β β (Fv F v), a * a' = 1 → b * b' = 1 →
      (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) = 1 := fun a b a' b' e1 e2 => by
    refine h.extM ?_ ?_ ?_
    · have : (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) - 1 =
          secM sec (a - 1) (b - 1) * (1 + secM sec (a' - 1) (b' - 1)) + secM sec (a' - 1) (b' - 1) := by noncomm_ring
      rw [this]
      exact ((h.atM _ _).kd_mul_right _).kd_add (h.atM _ _)
    · rw [Matrix.map_mul, k1, k1, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, k2, k2, e2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨1 + secM sec (g₁.1 - 1) (g₂.1 - 1), 1 + secM sec ((g₁⁻¹).1 - 1) ((g₂⁻¹).1 - 1), k3 _ _ _ _ g₁.mul_inv g₂.mul_inv,
    k3 _ _ _ _ g₁.inv_mul g₂.inv_mul⟩, ?_, k1 _ _, k2 _ _⟩
  rw [Units.val_mk, add_sub_cancel_left]
  exact h.atM _ _

/- English proof (translation)
Use `congrArg (fun m : Matrix β β (AE F E) => m.map (piW t)) (show ((g : GL β (AE F E)) : Matrix β β (AE F E))ᵀ * J * ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (cA σ) = J from g.2)` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map]`. Then use the resulting hypothesis.
-/
theorem unit_rel {J : Matrix β β (AE F E)} (g : UG (cA σ) J) :
    (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ * J.map (piW t) *
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)) = J.map (piW t) := by
  have := congrArg (fun m : Matrix β β (AE F E) => m.map (piW t))
    (show ((g : GL β (AE F E)) : Matrix β β (AE F E))ᵀ * J * ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (cA σ) = J from g.2)
  rwa [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map] at this

/- English proof (translation)
Take `⟨B, hB⟩` from `hu`. Set `gT : GL β (Fv F v)` to `⟨(g₀.1)ᵀ, ((g₀⁻¹).1)ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩`. Take `⟨g, ha, h1, h2⟩` from `h.exists_gl g₀ (B⁻¹ * gT⁻¹ * B)`. Establish `key : (g₀.1)ᵀ * B.1 * (B⁻¹ * gT⁻¹ * B).1 = B.1`. Establish `: gT * B * (B⁻¹ * gT⁻¹ * B) = B` using `by group`.

Conclude with `congrArg Units.val this`. Use `⟨⟨g, ?_⟩, ha, h1⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) = J`. Use `h.extM ?_ ?_ ?_` and prove the remaining obligations. Establish `e : (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) - J = ((g : Matrix β β (AE F E)) - 1)ᵀ * (J * (g : Matrix β β (AE F E)).map (cA σ)) + J * ((g : Matrix β β (AE F E)) - 1).map (cA σ)`.

Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), transpose_sub, transpose_one]`. Use `noncomm_ring`. Rewrite using `[e]`. Conclude with `(ha.kd_transpose.kd_mul_right _).kd_add (At.kd_mul_left (kd_at_matrix.2 fun i j => h.atConj _ (kd_at_matrix.1 ha i j)) _)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map, h1, h2, ← hB, key]`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, h.conj2, Matrix.transpose_map, h1, h2, hJ, ← hB, Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Use `congrArg Matrix.transpose key` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.
-/
theorem exists_ug {J : Matrix β β (AE F E)} {ε : Fv F v} (hJ : J.map (piW (t.comp σ)) = ε • (J.map (piW t))ᵀ)
    (hu : IsUnit (J.map (piW t))) (g₀ : GL β (Fv F v)) : ∃ g : UG (cA σ) J,
      At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1) ∧
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀ := by
  obtain ⟨B, hB⟩ := hu
  let gT : GL β (Fv F v) := ⟨(g₀.1)ᵀ, ((g₀⁻¹).1)ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl g₀ (B⁻¹ * gT⁻¹ * B)
  have key : (g₀.1)ᵀ * B.1 * (B⁻¹ * gT⁻¹ * B).1 = B.1 := by
    have : gT * B * (B⁻¹ * gT⁻¹ * B) = B := by group
    exact congrArg Units.val this
  refine ⟨⟨g, ?_⟩, ha, h1⟩
  change (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) = J
  refine h.extM ?_ ?_ ?_
  · have e : (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) - J =
        ((g : Matrix β β (AE F E)) - 1)ᵀ * (J * (g : Matrix β β (AE F E)).map (cA σ)) +
          J * ((g : Matrix β β (AE F E)) - 1).map (cA σ) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), transpose_sub, transpose_one]
      noncomm_ring
    rw [e]
    exact (ha.kd_transpose.kd_mul_right _).kd_add (At.kd_mul_left (kd_at_matrix.2 fun i j => h.atConj _ (kd_at_matrix.1 ha i j)) _)
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map, h1, h2, ← hB, key]
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj2, Matrix.transpose_map, h1, h2, hJ, ← hB, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have := congrArg Matrix.transpose key
    rwa [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this

/- English proof (translation)
Use `Subtype.ext (Units.ext (h.extM (by simpa using ha.kd_sub ha') e ?_))` and prove the remaining obligations. Establish `h1` using `h.unit_rel g`. Establish `h2` using `h.unit_rel g'`. Rewrite `h2` using `[← e]`. Establish `hg : IsUnit (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ` using `(Matrix.isUnit_transpose _).2 ((g : GL β (AE F E)).isUnit.map (piW t).mapMatrix)`.

Conclude with `(hg.mul hu).mul_left_cancel (h1.trans h2.symm)`.
-/
theorem ug_ext {J : Matrix β β (AE F E)} (hu : IsUnit (J.map (piW t))) {g g' : UG (cA σ) J}
    (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (ha' : At (evFin F v) (((g' : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (e : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = ((g' : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t)) :
    g = g' := by
  refine Subtype.ext (Units.ext (h.extM (by simpa using ha.kd_sub ha') e ?_))
  have h1 := h.unit_rel g
  have h2 := h.unit_rel g'
  rw [← e] at h2
  have hg : IsUnit (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ :=
    (Matrix.isUnit_transpose _).2 ((g : GL β (AE F E)).isUnit.map (piW t).mapMatrix)
  exact (hg.mul hu).mul_left_cancel (h1.trans h2.symm)

end IsSec

end PositivityTheory.KCo
