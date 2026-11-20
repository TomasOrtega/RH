import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLineComm.Bound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨b, hb, hbx⟩` from `HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Use `⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hb0`. Establish `h1` using `congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc`. Rewrite `h1` using `[map_mul, map_natCast]`. Rewrite using `[← h1, mul_assoc, mul_comm _ x]`. Conclude with `mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx`.
-/
theorem exists_nat_mul_mem_int (v : Pl F) (x : Fv F v) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, mul_assoc, mul_comm _ x]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) e`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hb' : algebraMap (𝓞 E) E b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Use `⟨Ideal.absNorm (Ideal.span {b}), a * c, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`. Establish `h1` using `congrArg (algebraMap (𝓞 E) E) hc`. Rewrite `h1` using `[map_mul, map_natCast]`. Rewrite using `[← h1, map_mul]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_nat_mul_int (e : E) : ∃ (k : ℕ) (o : 𝓞 E), k ≠ 0 ∧ (k : E) * e = algebraMap (𝓞 E) E o := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), a * c, ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, map_mul]
    field_simp

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin d → E))` using `by rw [hL.2]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨m1, h1, hy⟩` from `hy`. Take `⟨m2, h2, hz⟩` from `hz`. Use `⟨m1 * m2, mul_ne_zero h1 h2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hy m2`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hz m1`. Consider the case `smul e y _ hy`.

Take `⟨m, hm, hy⟩` from `hy`. Take `⟨k, o, hk, ho⟩` from `exists_nat_mul_int e`. Use `⟨k * m, mul_ne_zero hk hm, ?_⟩` and prove the remaining obligations. Establish `: (k * m) • (e • y) = o • (m • y)`. Rewrite using `[← algebraMap_smul E o (m • y), ← ho, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem o hy`.
-/
theorem exists_nat_smul_mem {d : ℕ} (L : Submodule (𝓞 E) (Fin d → E)) (hL : L.IsLattice E) (x : Fin d → E) :
    ∃ m : ℕ, m ≠ 0 ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin d → E)) := by rw [hL.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m1, h1, hy⟩ := hy
    obtain ⟨m2, h2, hz⟩ := hz
    refine ⟨m1 * m2, mul_ne_zero h1 h2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hy m2
    · rw [mul_smul]; exact nsmul_mem hz m1
  | smul e y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, o, hk, ho⟩ := exists_nat_mul_int e
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have : (k * m) • (e • y) = o • (m • y) := by
      rw [← algebraMap_smul E o (m • y), ← ho, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul,
        smul_smul]
      congr 1; push_cast; ring
    rw [this]
    exact L.smul_mem o hy

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert a S ha ih`. Take `⟨n1, h1, e1⟩` from `h a (Finset.mem_insert_self a S)`. Take `⟨n2, h2, e2⟩` from `ih fun s hs => h s (Finset.mem_insert_of_mem hs)`.

Use `⟨n1 * n2, mul_ne_zero h1 h2, fun s hs => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hs with rfl | hs` into its components or cases. Rewrite using `[mul_comm, mul_smul]`. Conclude with `G.nsmul_mem e1 n2`. Rewrite using `[mul_smul]`.

Conclude with `G.nsmul_mem (e2 s hs) n1`.
-/
theorem exists_common_nsmul {V α : Type} [AddCommGroup V] (G : AddSubgroup V) (S : Finset α) (f : α → V)
    (h : ∀ s ∈ S, ∃ n : ℕ, n ≠ 0 ∧ n • f s ∈ G) : ∃ n : ℕ, n ≠ 0 ∧ ∀ s ∈ S, n • f s ∈ G := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a S ha ih =>
    obtain ⟨n1, h1, e1⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨n2, h2, e2⟩ := ih fun s hs => h s (Finset.mem_insert_of_mem hs)
    refine ⟨n1 * n2, mul_ne_zero h1 h2, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · rw [mul_comm, mul_smul]; exact G.nsmul_mem e1 n2
    · rw [mul_smul]; exact G.nsmul_mem (e2 s hs) n1

end GlobalTheory.SphLineComm.Bound

end

noncomputable section

namespace GlobalTheory.SphLineComm.Bound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def satHat {d : ℕ} (W : Spc F E d) : AddSubgroup (Fin d → AE F E) where
  carrier := {y | ∃ n : ℕ, n ≠ 0 ∧ n • y ∈ latHat W}
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro y z ⟨n1, h1, hy⟩ ⟨n2, h2, hz⟩
    refine ⟨n1 * n2, mul_ne_zero h1 h2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact (latHat W).nsmul_mem hy n2
    · rw [mul_smul]; exact (latHat W).nsmul_mem hz n1
  neg_mem' := by
    rintro y ⟨n, h, hy⟩
    exact ⟨n, h, by rw [smul_neg]; exact neg_mem hy⟩

def atV (v : Pl F) (c : Fv F v) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v c)

/- English proof (translation)
Use `show LinearMap.inr F (Ainf F) (Af F) (singleFin v (a • c)) = a • atV v c`. Rewrite using `[map_smul, map_smul]`. Both sides reduce to the same expression.
-/
theorem atV_smul (v : Pl F) (a : F) (c : Fv F v) : atV v (a • c) = a • atV v c := by
  show LinearMap.inr F (Ainf F) (Af F) (singleFin v (a • c)) = a • atV v c
  rw [map_smul, map_smul]
  rfl

/- English proof (translation)
Use `Prod.ext (zero_mul _) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `singleFin v 1 * sndA F b = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F b))`. Use `Subtype.ext (funext fun u => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v 1 * sndA F b) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F b)))`. Rewrite using `[map_mul]`.

Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Rewrite using `[evalV_singleFin_self, evalV_singleFin_self, one_mul]`. Rewrite using `[evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]`.
-/
theorem unitAt_mul (v : Pl F) (b : AF F) :
    GlobalTheory.SphLineComm.unitAt v * b = atV v (evFin F v b) := by
  refine Prod.ext (zero_mul _) ?_
  change singleFin v 1 * sndA F b = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F b))
  refine Subtype.ext (funext fun u => ?_)
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v 1 * sndA F b) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F b)))
  rw [map_mul]
  by_cases e : u = v
  · subst e; rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
  · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]

/- English proof (translation)
Take `⟨m, hm, hx⟩` from `exists_nat_smul_mem W.L hL (Pi.single i f)`. Take `⟨N, hN, hc⟩` from `exists_nat_mul_mem_int v c`. Use `⟨N * m, mul_ne_zero hN hm, AddSubgroup.subset_closure ⟨atV v ((N : Fv F v) * c), ?_, fun w => ?_, m • Pi.single i f, hx, ?_⟩⟩` and prove the remaining obligations. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`.

Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v ((N : Fv F v) * c)) ∈ _`. Distinguish the cases in `e : w = v`. Substitute `e` using the available equality. Rewrite using `[evalV_singleFin_self]`. Conclude with `hc`.

Rewrite using `[evalV_singleFin_ne e]`. Conclude with `zero_mem _`. Use function extensionality and compare the values at `j`. Establish `hN' : (N : Fv F v) * c = (N : F) • c` using `by rw [Algebra.smul_def, map_natCast]`. Express the relevant statement in the definitionally equal form `(N * m) • (Pi.single i (atV v c ⊗ₜ[F] f) : Fin d → AE F E) j = atV v ((N : Fv F v) * c) • ((1 : AF F) ⊗ₜ[F] ((m • Pi.single i f : Fin d → E) j))`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, Pi.smul_apply, hN', atV_smul]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F (m : ℕ) f, TensorProduct.smul_tmul_smul]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero, smul_zero, TensorProduct.tmul_zero]`.
-/
theorem single_tmul_mem {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) (c : Fv F v) (f : E) (i : Fin d) :
    (Pi.single i (atV v c ⊗ₜ[F] f) : Fin d → AE F E) ∈ satHat W := by
  classical
  obtain ⟨m, hm, hx⟩ := exists_nat_smul_mem W.L hL (Pi.single i f)
  obtain ⟨N, hN, hc⟩ := exists_nat_mul_mem_int v c
  refine ⟨N * m, mul_ne_zero hN hm, AddSubgroup.subset_closure
    ⟨atV v ((N : Fv F v) * c), ?_, fun w => ?_, m • Pi.single i f, hx, ?_⟩⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v ((N : Fv F v) * c)) ∈ _
    by_cases e : w = v
    · subst e; rw [evalV_singleFin_self]; exact hc
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · funext j
    have hN' : (N : Fv F v) * c = (N : F) • c := by rw [Algebra.smul_def, map_natCast]
    change (N * m) • (Pi.single i (atV v c ⊗ₜ[F] f) : Fin d → AE F E) j =
      atV v ((N : Fv F v) * c) • ((1 : AF F) ⊗ₜ[F] ((m • Pi.single i f : Fin d → E) j))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Pi.smul_apply, hN', atV_smul]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F (m : ℕ) f,
        TensorProduct.smul_tmul_smul]
      push_cast; rfl
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero, smul_zero, TensorProduct.tmul_zero]

end GlobalTheory.SphLineComm.Bound

end

noncomputable section

namespace GlobalTheory.SphLineComm.Bound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero, Pi.single_zero]`. Conclude with `zero_mem _`. Consider the case `tmul b f`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, unitAt_mul]`.

Conclude with `single_tmul_mem W hL v _ f i`. Consider the case `add s t hs ht => rw [smul_add, Pi.single_add]`. Conclude with `add_mem hs ht`.
-/
theorem single_unitAt_smul_mem {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) (i : Fin d) (t : AE F E) :
    (Pi.single i (GlobalTheory.SphLineComm.unitAt v • t) : Fin d → AE F E) ∈ satHat W := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, Pi.single_zero]; exact zero_mem _
  | tmul b f =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, unitAt_mul]
    exact single_tmul_mem W hL v _ f i
  | add s t hs ht => rw [smul_add, Pi.single_add]; exact add_mem hs ht

/- English proof (translation)
Establish `h1 : (1 - GlobalTheory.SphLineComm.unitAt v) • y = 0` using `hy _ (by rw [map_sub, map_one, GlobalTheory.SphLineComm.evFin_unitAt_self, sub_self])`. Establish `h2 : y = GlobalTheory.SphLineComm.unitAt v • y`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h1`. Rewrite using `[h2, ← Finset.univ_sum_single (GlobalTheory.SphLineComm.unitAt v • y)]`.

Conclude with `sum_mem fun i _ => single_unitAt_smul_mem W hL v i (y i)`.
-/
theorem mem_satHat_of_at {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) (y : Fin d → AE F E)
    (hy : At (evFin F v) y) : y ∈ satHat W := by
  have h1 : (1 - GlobalTheory.SphLineComm.unitAt v) • y = 0 :=
    hy _ (by rw [map_sub, map_one, GlobalTheory.SphLineComm.evFin_unitAt_self, sub_self])
  have h2 : y = GlobalTheory.SphLineComm.unitAt v • y := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1; exact h1
  rw [h2, ← Finset.univ_sum_single (GlobalTheory.SphLineComm.unitAt v • y)]
  exact sum_mem fun i _ => single_unitAt_smul_mem W hL v i (y i)

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show inclR (F := F) (AF F) (algebraMap (𝓞 E) E o * x i) = inclR (F := F) (AF F) (algebraMap (𝓞 E) E o) * inclR (F := F) (AF F) (x i)`. Conclude with `map_mul _ _ _`.
-/
theorem incV_smul {d : ℕ} (o : 𝓞 E) (x : Fin d → E) :
    incV F (o • x) = inclR (F := F) (AF F) (algebraMap (𝓞 E) E o) • incV F x := by
  funext i
  show inclR (F := F) (AF F) (algebraMap (𝓞 E) E o * x i) = inclR (F := F) (AF F) (algebraMap (𝓞 E) E o) * inclR (F := F) (AF F) (x i)
  exact map_mul _ _ _

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hav, o • x, W.L.smul_mem o hx, ?_⟩` and prove the remaining obligations. Rewrite using `[incV_smul, smul_comm]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
theorem int_smul_mem_latHat {d : ℕ} (W : Spc F E d) (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latHat W) :
    inclR (F := F) (AF F) (algebraMap (𝓞 E) E o) • z ∈ latHat W := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, o • x, W.L.smul_mem o hx, ?_⟩
    rw [incV_smul, smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `F E _ _ _ _ _ d W v M hL hM`. Establish `hsupp : ∀ x : Fin d → E, At (evFin F v) (M *ᵥ incV F x)` using `fun x u hu => by`. Rewrite using `[← Matrix.smul_mulVec, hM u hu, Matrix.zero_mulVec]`. Take `⟨S, hS⟩` from `hL.1`. Take `⟨n, hn, hnS⟩` from `exists_common_nsmul (latHat W) S (fun x => M *ᵥ incV F x) fun s _ => mem_satHat_of_at W hL v _ (hsupp s)`.

Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hgen : ∀ x ∈ W.L, n • (M *ᵥ incV F x) ∈ latHat W`. Introduce `x hx`. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact hnS y hy`. Consider the case `zero`. Establish `: incV F (0 : Fin d → E) = 0` using `funext fun i => map_zero (inclR (F := F) (AF F))`. Rewrite using `[this, Matrix.mulVec_zero, smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz`. Establish `: incV F (y + z) = incV F y + incV F z` using `funext fun i => map_add (inclR (F := F) (AF F)) (y i) (z i)`. Rewrite using `[this, Matrix.mulVec_add, smul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul o y _ hy`.

Rewrite using `[incV_smul, Matrix.mulVec_smul, smul_comm]`. Conclude with `int_smul_mem_latHat W o hy`. Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, hav, x, hx, rfl⟩` from `hz`. Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Conclude with `GlobalTheory.SphLineComm.smul_mem_latHat W a ha hav (hgen x hx)`. Consider the case `zero => rw [Matrix.mulVec_zero, smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [Matrix.mulVec_neg, smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem nsmul_mulVec_mem_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d) (v : Pl F)
    (M : Matrix (Fin d) (Fin d) (AE F E)), W.L.IsLattice E → At (evFin F v) M →
    ∃ n : ℕ, n ≠ 0 ∧ ∀ z ∈ latHat W, n • (M *ᵥ z) ∈ latHat W := by
  intro F E _ _ _ _ _ d W v M hL hM
  have hsupp : ∀ x : Fin d → E, At (evFin F v) (M *ᵥ incV F x) := fun x u hu => by
    rw [← Matrix.smul_mulVec, hM u hu, Matrix.zero_mulVec]
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨n, hn, hnS⟩ := exists_common_nsmul (latHat W) S (fun x => M *ᵥ incV F x)
    fun s _ => mem_satHat_of_at W hL v _ (hsupp s)
  refine ⟨n, hn, ?_⟩
  have hgen : ∀ x ∈ W.L, n • (M *ᵥ incV F x) ∈ latHat W := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hnS y hy
    | zero =>
      have : incV F (0 : Fin d → E) = 0 := funext fun i => map_zero (inclR (F := F) (AF F))
      rw [this, Matrix.mulVec_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : incV F (y + z) = incV F y + incV F z := funext fun i => map_add (inclR (F := F) (AF F)) (y i) (z i)
      rw [this, Matrix.mulVec_add, smul_add]; exact add_mem hy hz
    | smul o y _ hy =>
      rw [incV_smul, Matrix.mulVec_smul, smul_comm]
      exact int_smul_mem_latHat W o hy
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, rfl⟩ := hz
    rw [Matrix.mulVec_smul, smul_comm]
    exact GlobalTheory.SphLineComm.smul_mem_latHat W a ha hav (hgen x hx)
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.SphLineComm.Bound

end
