import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameA
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open PositivityTheory.ThKH.Iwas Hgt
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

/- English proof (translation)
Use `(hv _).1 fun y hy => ?_` and prove the remaining obligations. Use `GlobalTheory.LatVacArith.psi_int hψ (Algebra.trace F E z) (fun a => ?_) (singleFin v y) (fun u => ?_)` as an intermediate fact. Use `Eq.trans (congrArg (fun t : Af F => ψ (pairA F 0 t)) (af_ext fun u => ?_)) this` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v _) = _`. Rewrite using `[map_mul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u)]`.

Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Rewrite using `[evalV_singleFin_self, evalV_singleFin_self, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]`.

Take `⟨k, hk⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (hz (algebraMap (𝓞 F) (𝓞 E) a))`. Use `⟨k, Eq.trans ?_ hk.symm⟩` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v y) ∈ _`.

Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Rewrite using `[evalV_singleFin_self]` and apply the resulting hypothesis. Rewrite using `[evalV_singleFin_ne e]`. Conclude with `zero_mem _`.
-/
theorem trace_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hv : PsiUnr ψ v) {z : E} (hz : InD z) :
    algebraMap F (Fv F v) (Algebra.trace F E z) ∈ v.adicCompletionIntegers F := by
  refine (hv _).1 fun y hy => ?_
  have := GlobalTheory.LatVacArith.psi_int hψ (Algebra.trace F E z) (fun a => ?_) (singleFin v y) (fun u => ?_)
  · refine Eq.trans (congrArg (fun t : Af F => ψ (pairA F 0 t)) (af_ext fun u => ?_)) this
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v _) = _
    rw [map_mul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u)]
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, evalV_singleFin_self, mul_comm]; rfl
    · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]
  · obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (hz (algebraMap (𝓞 F) (𝓞 E) a))
    refine ⟨k, Eq.trans ?_ hk.symm⟩
    rw [← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def]
    rfl
  · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v y) ∈ _
    by_cases e : u = v
    · subst e; rwa [evalV_singleFin_self]
    · rw [evalV_singleFin_ne e]; exact zero_mem _

/- English proof (translation)
Use `trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := z)` as an intermediate fact. Set `τ` to `IsScalarTower.toAlgHom F E (AlgebraicClosure E)`. Apply `(τ : E →+* AlgebraicClosure E).injective` to reduce the goal to its premises. Rewrite `this` using `[show (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} from Finset.ext fun ρ => by simpa using eq_or_eq_comp_conj h τ ρ, Finset.sum_pair (comp_conj_ne h τ).symm]`. Rewrite using `[map_add]`.

Conclude with `this.symm.trans (τ.commutes _).symm`.
-/
theorem add_conj (h : IsCMExt F E σ) (z : E) : z + σ z = algebraMap F E (Algebra.trace F E z) := by
  classical
  have := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := z)
  let τ := IsScalarTower.toAlgHom F E (AlgebraicClosure E)
  apply (τ : E →+* AlgebraicClosure E).injective
  rw [show (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} from
    Finset.ext fun ρ => by simpa using eq_or_eq_comp_conj h τ ρ, Finset.sum_pair (comp_conj_ne h τ).symm] at this
  rw [map_add]
  exact this.symm.trans (τ.commutes _).symm

/- English proof (translation)
Use `set Z := inclR (F := F) (Fv F v) z`. Establish `key : ∀ y ∈ intLoc F E v, y * Z + sigR _ σ (y * Z) ∈ intLoc F E v` using `fun y hy => by`. Use `intLoc_induction (p := fun y => y * Z + sigR _ σ (y * Z) ∈ intLoc F E v) (fun a ha x => ?_) (by simp) (fun _ _ h h' => by convert add_mem h h' using 1; simp only [add_mul, map_add]; ring) (fun _ h => by convert neg_mem h using 1; simp only [neg_mul, map_neg]; ring) hy` and prove the remaining obligations. Use `tmul_mem_intLoc (mul_mem ha (trace_mem hB.std (hB.inert v w hw).2.2 (hz.mul x))) 1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[show a ⊗ₜ[F] (x : E) * Z = a ⊗ₜ[F] (z * x) from (Algebra.TensorProduct.tmul_mul_tmul a 1 _ z).trans (by rw [mul_one, mul_comm])]`.

Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] (z * x) + a ⊗ₜ[F] σ (z * x) = _`. Rewrite using `[← TensorProduct.tmul_add, add_conj hB.cm, mul_comm a, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression. Establish `hu : w.under (𝓞 F) = v` using `(under_eq_iff hw w).2 rfl`. Take `⟨c, hc, -⟩` from `existsUnique_isConjAt σ hw hu`.

Take `⟨ϖ, -, -, -, -, ⟨x, hx, hx1⟩, -⟩` from `exists_isUnramInv hB.cm hw hc`. Take `⟨y, rfl⟩` from `(toCompl_bijective hw hu).2 x`. Establish `hy` using `(mem_intLoc_iff hw hu y).2 hx`. Establish `h1` using `(mem_intLoc_iff hw hu _).1 (sub_mem (mul_mem (sigR_mem_intLoc σ hy) (key 1 (one_mem _))) (key y hy))`. Rewrite using `[show sigR _ σ y * (1 * Z + sigR _ σ (1 * Z)) - (y * Z + sigR _ σ (y * Z)) = (sigR _ σ y - y) * Z by`.

Simplify using `only [one_mul, map_mul]`. Use the proof step `ring, map_mul, map_sub, ← hc] at h1`. Use `(mem_intLoc_iff hw hu _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_)` and prove the remaining obligations. Establish `h2` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1`. Rewrite `h2` using `[map_mul, hx1, one_mul]`. Then use the resulting hypothesis.
-/
theorem inD_mem {B : Base F E} (hB : B.IsGood σ) {w : Pl E} (hw : Formalism.UG.IsInertAt F E v w) {z : E} (hz : InD z) :
    inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  set Z := inclR (F := F) (Fv F v) z
  have key : ∀ y ∈ intLoc F E v, y * Z + sigR _ σ (y * Z) ∈ intLoc F E v := fun y hy => by
    refine intLoc_induction (p := fun y => y * Z + sigR _ σ (y * Z) ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun _ _ h h' => by convert add_mem h h' using 1; simp only [add_mul, map_add]; ring)
      (fun _ h => by convert neg_mem h using 1; simp only [neg_mul, map_neg]; ring) hy
    convert tmul_mem_intLoc (mul_mem ha (trace_mem hB.std (hB.inert v w hw).2.2 (hz.mul x))) 1 using 1
    rw [show a ⊗ₜ[F] (x : E) * Z = a ⊗ₜ[F] (z * x) from (Algebra.TensorProduct.tmul_mul_tmul a 1 _ z).trans (by rw [mul_one, mul_comm])]
    change a ⊗ₜ[F] (z * x) + a ⊗ₜ[F] σ (z * x) = _
    rw [← TensorProduct.tmul_add, add_conj hB.cm, mul_comm a, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]
    rfl
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, -, -, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hB.cm hw hc
  obtain ⟨y, rfl⟩ := (toCompl_bijective hw hu).2 x
  have hy := (mem_intLoc_iff hw hu y).2 hx
  have h1 := (mem_intLoc_iff hw hu _).1 (sub_mem (mul_mem (sigR_mem_intLoc σ hy) (key 1 (one_mem _))) (key y hy))
  rw [show sigR _ σ y * (1 * Z + sigR _ σ (1 * Z)) - (y * Z + sigR _ σ (y * Z)) = (sigR _ σ y - y) * Z by
    simp only [one_mul, map_mul]; ring, map_mul, map_sub, ← hc] at h1
  refine (mem_intLoc_iff hw hu _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  rwa [map_mul, hx1, one_mul] at h2

variable (σ v) in

def Uni (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v ⊗[F] E)) : Prop :=
  Int (intLoc F E v) (g.1ᵀ * J.map (inclR (F := F) (Fv F v)) * g.1.map (sigR _ σ)) ∧
    ∃ G', Int (intLoc F E v) G' ∧ G' * (g.1ᵀ * J.map (inclR (F := F) (Fv F v)) * g.1.map (sigR _ σ)) = 1

/- English proof (translation)
Establish `hc` using `hB.cm`. Establish `hσ` using `cm_conj_conj hc`. Establish `hL : Y.L.IsLattice E` using `hY.elim (·.lat) (·.lat)`. Take `⟨P, h1, h2⟩` from `Frames.exists_rational_frame Y.L v`. Set `ι` to `inclR (F := F) (E := E) (Fv F v)`.

Use `set G := P.1ᵀ * Y.J * P.1.map σ with hG`. Establish `eG : (bc ι P).1ᵀ * Y.J.map ι * (bc ι P).1.map (sigR _ σ) = G.map ι`. Rewrite using `[hG, Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Establish `one : ∀ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 → G'.map ι * G.map ι = 1` using `fun G' h => by`.

Rewrite using `[← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]`. It suffices to establish `h : ∃ l : (Fv F v ⊗[F] E)ˣ, Int (intLoc F E v) (((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι) ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 ∧ Int (intLoc F E v) ((l.1 * sigR _ σ l.1) • G'.map ι) by`. Take `⟨l, a1, G', a2, a3⟩` from `h`. Establish `e : (l⁻¹ • bc ι P).1ᵀ * Y.J.map ι * (l⁻¹ • bc ι P).1.map (sigR _ σ) = ((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι`. Rewrite using `[← eG, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul]`.

Use `congr 1`. Conclude with `Matrix.ext fun i j => map_mul (sigR (Fv F v) σ) (l⁻¹).1 _`. Use `⟨bc ι P, l⁻¹ • bc ι P, l, Frames.frame_of_rational P h1 h2, (smul_inv_smul l _).symm, e ▸ a1, _, a3, ?_⟩` and prove the remaining obligations. Rewrite using `[e, Matrix.smul_mul, Matrix.mul_smul, one G' a2, smul_smul, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul, one_smul]`. Break down `hY with h | h` into its components or cases.

Take `⟨G', b0, b1, b2⟩` from `gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2`. Conclude with `⟨1, fun i j => by simpa using (b1 i j).mem, G', b0, fun i j => by simpa using (b2 i j).mem⟩`. Take `⟨δ, d0, d1, d2⟩` from `exists_locGen (E := E) v`. Take `⟨G', b0, b1, b2⟩` from `gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2`. Rewrite `b0`, `b1` using `[← hG]`.

Break down `GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩` into its components or cases. Establish `s1 : (G.map σ)ᵀ = -G` using `(gram_sym (σ : E →+* E) hσ (ε := -1) (Matrix.ext fun i j => (h.skew i j).trans (neg_one_mul _).symm) P.1).trans (neg_one_smul _ _)`. Establish `s2 : (G'.map σ)ᵀ = -G'`. Establish `e : (G.map σ)ᵀ * (G'.map σ)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul]`.

Express the relevant statement in the definitionally equal form `(G'.map (σ : E →+* E) * G.map (σ : E →+* E))ᵀ = 1`. Rewrite using `[← Matrix.map_mul, b0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Rewrite using `[← Matrix.one_mul (G'.map σ)ᵀ, ← b0, Matrix.mul_assoc, ← neg_neg G, ← s1, Matrix.neg_mul, e]`. Simplify using the standard rewrite rules. Set `u` to `(splitAlgEquiv hc τ).symm`.

Establish `fin : ∀ (d : E) (X : Matrix (Fin n) (Fin n) E), (X.map σ)ᵀ = -X → (∀ i j, LocInt v (d * X i j)) → Int (intLoc F E v) ((u (τ d, 1) * sigR _ σ (u (τ d, 1))) • X.map ι)` using `fun d X hX hd i j => by`. Establish `q : ∀ i j, τ d * τ (X i j) ∈ v.adicCompletionIntegers F` using `fun i j => by`. Simplify `splitProj_mem τ (hd i j).mem` using `[inclR]`. Establish `q' : σ (X i j) = -X j i` using `congrFun (congrFun hX j) i`. Use `(mem_intLoc_iff_split hc τ).2 ⟨?_, ?_⟩` and prove the remaining obligations.

Simplify `q i j` using `[u, ι, inclR, ← splitProj_comp]`. Simplify `q j i` using `[u, ι, inclR, splitProj_comp_sigR hc, q']`. Establish `e : u (τ δ, 1) * u (τ δ⁻¹, 1) = 1`. Rewrite using `[← map_mul, Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ d0, map_one, mul_one]`. Conclude with `map_one u`.

Conclude with `⟨⟨_, _, e, (mul_comm _ _).trans e⟩, fin _ _ s1 b1, G', b0, fin _ _ s2 b2⟩`. Establish `i1` using `inD_mem hB hw d1`. Establish `i2` using `(d2 1 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))).mem`. Use `⟨1, fun i j => ?_, G', b0, fun i j => ?_⟩` and prove the remaining obligations. Simplify `mul_mem i1 (b1 i j).mem` using `[← map_mul, d0]`.

Simplify `mul_mem i2 (b2 i j).mem` using `[← map_mul, d0]`.
-/
theorem exists_loc {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (v : Pl F) : ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)) (l : (Fv F v ⊗[F] E)ˣ),
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := by
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  let ι := inclR (F := F) (E := E) (Fv F v)
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  have eG : (bc ι P).1ᵀ * Y.J.map ι * (bc ι P).1.map (sigR _ σ) = G.map ι := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]; rfl
  have one : ∀ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 → G'.map ι * G.map ι = 1 := fun G' h => by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  suffices h : ∃ l : (Fv F v ⊗[F] E)ˣ, Int (intLoc F E v) (((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι) ∧
      ∃ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 ∧ Int (intLoc F E v) ((l.1 * sigR _ σ l.1) • G'.map ι) by
    obtain ⟨l, a1, G', a2, a3⟩ := h
    have e : (l⁻¹ • bc ι P).1ᵀ * Y.J.map ι * (l⁻¹ • bc ι P).1.map (sigR _ σ) = ((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι := by
      rw [← eG, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul]
      congr 1
      exact Matrix.ext fun i j => map_mul (sigR (Fv F v) σ) (l⁻¹).1 _
    refine ⟨bc ι P, l⁻¹ • bc ι P, l, Frames.frame_of_rational P h1 h2, (smul_inv_smul l _).symm, e ▸ a1, _, a3, ?_⟩
    rw [e, Matrix.smul_mul, Matrix.mul_smul, one G' a2, smul_smul, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul, one_smul]
  rcases hY with h | h
  · obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
      isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2
    exact ⟨1, fun i j => by simpa using (b1 i j).mem, G', b0, fun i j => by simpa using (b2 i j).mem⟩
  obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
  obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2
  rw [← hG] at b0 b1
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have s1 : (G.map σ)ᵀ = -G := (gram_sym (σ : E →+* E) hσ (ε := -1)
      (Matrix.ext fun i j => (h.skew i j).trans (neg_one_mul _).symm) P.1).trans (neg_one_smul _ _)
    have s2 : (G'.map σ)ᵀ = -G' := by
      have e : (G.map σ)ᵀ * (G'.map σ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        change (G'.map (σ : E →+* E) * G.map (σ : E →+* E))ᵀ = 1
        rw [← Matrix.map_mul, b0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
      rw [← Matrix.one_mul (G'.map σ)ᵀ, ← b0, Matrix.mul_assoc, ← neg_neg G, ← s1, Matrix.neg_mul, e]; simp
    let u := (splitAlgEquiv hc τ).symm
    have fin : ∀ (d : E) (X : Matrix (Fin n) (Fin n) E), (X.map σ)ᵀ = -X → (∀ i j, LocInt v (d * X i j)) →
        Int (intLoc F E v) ((u (τ d, 1) * sigR _ σ (u (τ d, 1))) • X.map ι) := fun d X hX hd i j => by
      have q : ∀ i j, τ d * τ (X i j) ∈ v.adicCompletionIntegers F := fun i j => by
        simpa [inclR] using splitProj_mem τ (hd i j).mem
      have q' : σ (X i j) = -X j i := congrFun (congrFun hX j) i
      refine (mem_intLoc_iff_split hc τ).2 ⟨?_, ?_⟩
      · simpa [u, ι, inclR, ← splitProj_comp] using q i j
      · simpa [u, ι, inclR, splitProj_comp_sigR hc, q'] using q j i
    have e : u (τ δ, 1) * u (τ δ⁻¹, 1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ d0, map_one, mul_one]; exact map_one u
    exact ⟨⟨_, _, e, (mul_comm _ _).trans e⟩, fin _ _ s1 b1, G', b0, fin _ _ s2 b2⟩
  · have i1 := inD_mem hB hw d1
    have i2 := (d2 1 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))).mem
    refine ⟨1, fun i j => ?_, G', b0, fun i j => ?_⟩
    · simpa [← map_mul, d0] using mul_mem i1 (b1 i j).mem
    · simpa [← map_mul, d0] using mul_mem i2 (b2 i j).mem

/- English proof (translation)
Take `⟨m, hm, hi⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple`. Use `(Ideal.finite_factors (I := Ideal.span {(m : 𝓞 F)}) (by simpa using hm)).subset fun v hv => by_contra fun h => hv ?_` and prove the remaining obligations. Conclude with `⟨m, fun k => h (Ideal.dvd_span_singleton.2 k), ⟨_, hi⟩, by simp⟩`.
-/
theorem ae_locInt (z : E) : ∀ᶠ v : Pl F in cofinite, LocInt v z := by
  obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple
  refine (Ideal.finite_factors (I := Ideal.span {(m : 𝓞 F)}) (by simpa using hm)).subset fun v hv => by_contra fun h => hv ?_
  exact ⟨m, fun k => h (Ideal.dvd_span_singleton.2 k), ⟨_, hi⟩, by simp⟩

/- English proof (translation)
Establish `hL : Y.L.IsLattice E` using `hY.elim (·.lat) (·.lat)`. Take `⟨S, hS⟩` from `Frames.exists_finset_latLoc_eq (F := F) Y.L`. Establish `h0 : ∀ᶠ v : Pl F in cofinite, v ∉ S ∧ ∀ i j, LocInt v (Y.J i j) ∧ LocInt v (Y.J⁻¹ i j)` using `S.eventually_cofinite_notMem.and (eventually_all.2 fun i => eventually_all.2 fun j => (ae_locInt _).and (ae_locInt _))`. Establish `key : ∀ v : Pl F, ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)), (v ∉ Set.Finite.toFinset h0 → a = 1 ∧ g = 1) ∧ ∃ l : (Fv F v ⊗[F] E)ˣ, (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g` using `fun v => by`. Distinguish the cases in `hv : v ∈ Set.Finite.toFinset h0`.

Take `⟨a, g, h⟩` from `exists_loc hB hY hJ v`. Conclude with `⟨a, g, fun h => absurd hv h, h⟩`. Establish `hv'` using `not_not.1 (mt (Set.Finite.mem_toFinset h0).2 hv)`. Use `⟨1, 1, fun _ => ⟨rfl, rfl⟩, 1, fun y => by simpa using hS v hv'.1 y, (one_smul _ _).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Uni, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`.

Use `⟨fun i j => (hv'.2 i j).1.mem, Y.J⁻¹.map (inclR (F := F) (Fv F v)), fun i j => (hv'.2 i j).2.mem, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `choose a g h1 l h2 h3 h4 using key`. Set `e` to `fun w => RingEquiv.ofBijective _ (infEmb_bijective hB.cm (B.emb w))`. Take `⟨a', ha, -⟩` from `Frames.exists_GL_of_components _ a (fun v hv => (h1 v hv).1) fun _ => 1`.

Take `⟨g', hg, hg'⟩` from `Frames.exists_GL_of_components _ g (fun v hv => (h1 v hv).2) fun w => bc (e w).symm.toRingHom (c w)`. Use `⟨a', g', fun v y => ha v ▸ h2 v y, fun v => ?_, fun w => Units.ext (Matrix.ext fun i j => ?_)⟩` and prove the remaining obligations. Rewrite using `[ha, hg]`. Conclude with `⟨⟨_, h3 v⟩, h4 v⟩`. Conclude with `(congrArg (fun x => e w (x.1 i j)) (hg' w)).trans ((e w).apply_symm_apply _)`.
-/
theorem exists_ad {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (c : InfinitePlace F → GL (Fin n) ℂ) : ∃ a g : GL (Fin n) (AE F E), IsLatticeFrame Y.L a ∧
      (∀ v, (∃ l : (Fv F v ⊗[F] E)ˣ, (bc (compFin F E v) a).1 = l.1 • (bc (compFin F E v) g).1) ∧ Uni σ v Y.J (bc (compFin F E v) g)) ∧
      ∀ w, bc (piInf (B.emb w)) g = c w := by
  classical
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨S, hS⟩ := Frames.exists_finset_latLoc_eq (F := F) Y.L
  have h0 : ∀ᶠ v : Pl F in cofinite, v ∉ S ∧ ∀ i j, LocInt v (Y.J i j) ∧ LocInt v (Y.J⁻¹ i j) :=
    S.eventually_cofinite_notMem.and (eventually_all.2 fun i => eventually_all.2 fun j => (ae_locInt _).and (ae_locInt _))
  have key : ∀ v : Pl F, ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)), (v ∉ Set.Finite.toFinset h0 → a = 1 ∧ g = 1) ∧ ∃ l : (Fv F v ⊗[F] E)ˣ,
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := fun v => by
    by_cases hv : v ∈ Set.Finite.toFinset h0
    · obtain ⟨a, g, h⟩ := exists_loc hB hY hJ v
      exact ⟨a, g, fun h => absurd hv h, h⟩
    · have hv' := not_not.1 (mt (Set.Finite.mem_toFinset h0).2 hv)
      refine ⟨1, 1, fun _ => ⟨rfl, rfl⟩, 1, fun y => by simpa using hS v hv'.1 y, (one_smul _ _).symm, ?_⟩
      rw [Uni, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      refine ⟨fun i j => (hv'.2 i j).1.mem, Y.J⁻¹.map (inclR (F := F) (Fv F v)), fun i j => (hv'.2 i j).2.mem, ?_⟩
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  choose a g h1 l h2 h3 h4 using key
  let e := fun w => RingEquiv.ofBijective _ (infEmb_bijective hB.cm (B.emb w))
  obtain ⟨a', ha, -⟩ := Frames.exists_GL_of_components _ a (fun v hv => (h1 v hv).1) fun _ => 1
  obtain ⟨g', hg, hg'⟩ := Frames.exists_GL_of_components _ g (fun v hv => (h1 v hv).2) fun w => bc (e w).symm.toRingHom (c w)
  refine ⟨a', g', fun v y => ha v ▸ h2 v y, fun v => ?_, fun w => Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [ha, hg]; exact ⟨⟨_, h3 v⟩, h4 v⟩
  · exact (congrArg (fun x => e w (x.1 i j)) (hg' w)).trans ((e w).apply_symm_apply _)

end GlobalTheory.ThK.Dbl.Frame

end
