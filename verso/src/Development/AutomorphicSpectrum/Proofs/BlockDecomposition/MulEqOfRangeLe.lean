import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.TorusCh

def IsPol {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop := ∃ f : K[X], e = aeval γ f

structure IsPrim {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop where
  pol : IsPol γ e
  idem : e * e = e
  ne : e ≠ 0
  inv : ∀ h : K[X], aeval γ h * e ≠ 0 → ∃ h' : K[X], aeval γ h' * (aeval γ h * e) = e

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  d.val * (X.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val

def rm (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (Ad E) := X.map (algebraMap E (Ad E))

def chi (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : Ad E := (1 + rm e * (t.val - 1)).det

def lam (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : ℝ := logAbs (chi e t)

section Pol

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Take `⟨f, rfl⟩` from `ha`. Take `⟨g, rfl⟩` from `hb`. Rewrite using `[← map_mul, mul_comm, map_mul]`.
-/
theorem pol_comm (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b) : a * b = b * a := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  rw [← map_mul, mul_comm, map_mul]

/- English proof (translation)
Rewrite using `[Algebra.adjoin_singleton_eq_range_aeval]`. Conclude with `⟨fun ⟨f, h⟩ => ⟨f, h.symm⟩, fun ⟨f, h⟩ => ⟨f, h.symm⟩⟩`.
-/
theorem isPol_iff (γ e : Matrix (Fin n) (Fin n) K) : IsPol γ e ↔ e ∈ Algebra.adjoin K {γ} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨fun ⟨f, h⟩ => ⟨f, h.symm⟩, fun ⟨f, h⟩ => ⟨f, h.symm⟩⟩

/- English proof (translation)
Establish `hc : γ.val * p = p * γ.val` using `pol_comm γ.val _ _ ⟨X, (aeval_X _).symm⟩ hp`. Establish `hs : LinearMap.range (Matrix.toLin' γ.val) = ⊤`. Use `LinearMap.range_eq_top.2 fun y => ⟨(γ⁻¹ : GL (Fin n) K).val *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Unfold `img`.

Rewrite using `[← LinearMap.range_comp, ← Matrix.toLin'_mul, hc, Matrix.toLin'_mul, LinearMap.range_comp, hs, Submodule.map_top]`.
-/
theorem img_of_pol (γ : GL (Fin n) K) (p : Matrix (Fin n) (Fin n) K) (hp : IsPol γ.val p) :
    img γ (LinearMap.range (Matrix.toLin' p)) = LinearMap.range (Matrix.toLin' p) := by
  have hc : γ.val * p = p * γ.val := pol_comm γ.val _ _ ⟨X, (aeval_X _).symm⟩ hp
  have hs : LinearMap.range (Matrix.toLin' γ.val) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(γ⁻¹ : GL (Fin n) K).val *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  unfold img
  rw [← LinearMap.range_comp, ← Matrix.toLin'_mul, hc, Matrix.toLin'_mul, LinearMap.range_comp, hs, Submodule.map_top]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, ha]`. Introduce `h`. Conclude with `⟨w, by rw [Matrix.toLin'_apply, h]⟩`.
-/
theorem mem_range_idem {a : Matrix (Fin n) (Fin n) K} (ha : a * a = a) (w : Fin n → K) :
    w ∈ LinearMap.range (Matrix.toLin' a) ↔ a *ᵥ w = w := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ha]
  · intro h
    exact ⟨w, by rw [Matrix.toLin'_apply, h]⟩

/- English proof (translation)
Use `Matrix.toLin'.injective (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Establish `h1 : a *ᵥ y ∈ LinearMap.range (Matrix.toLin' b)` using `h ⟨y, by rw [Matrix.toLin'_apply]⟩`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`. Conclude with `(mem_range_idem hb _).1 h1`.
-/
theorem mul_eq_of_range_le {a b : Matrix (Fin n) (Fin n) K} (hb : b * b = b)
    (h : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b)) : b * a = a := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  have h1 : a *ᵥ y ∈ LinearMap.range (Matrix.toLin' b) := h ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact (mem_range_idem hb _).1 h1

/- English proof (translation)
Establish `hc` using `pol_comm γ a b ha hb`. Use `⟨fun h => by rw [hc]; exact mul_eq_of_range_le hb2 h, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `mul_eq_of_range_le hb2 h.le`. Establish `h2` using `mul_eq_of_range_le ha2 h.ge`. Rewrite using `[← h1, ← hc, h2]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, rfl⟩`. Use `⟨⟨b *ᵥ y, ?_⟩, ⟨a *ᵥ y, ?_⟩⟩` and prove the remaining obligations. Simplify using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec]`. Simplify using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]`.

Introduce and unpack `w ⟨h1, h2⟩`. Establish `h1'` using `(mem_range_idem ha2 w).1 h1`. Establish `h2'` using `(mem_range_idem hb2 w).1 h2`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h2', h1']`.
-/
theorem idem_facts (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b)
    (ha2 : a * a = a) (hb2 : b * b = b) :
    (LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) → a * b = a) ∧
    (LinearMap.range (Matrix.toLin' a) = LinearMap.range (Matrix.toLin' b) → a = b) ∧
    LinearMap.range (Matrix.toLin' (a * b)) =
      LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) := by
  have hc := pol_comm γ a b ha hb
  refine ⟨fun h => by rw [hc]; exact mul_eq_of_range_le hb2 h, fun h => ?_, ?_⟩
  · have h1 := mul_eq_of_range_le hb2 h.le
    have h2 := mul_eq_of_range_le ha2 h.ge
    rw [← h1, ← hc, h2]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine ⟨⟨b *ᵥ y, ?_⟩, ⟨a *ᵥ y, ?_⟩⟩
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]
    · rintro w ⟨h1, h2⟩
      have h1' := (mem_range_idem ha2 w).1 h1
      have h2' := (mem_range_idem hb2 w).1 h2
      refine ⟨w, ?_⟩
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h2', h1']

end Pol

section Chi

/- English proof (translation)
Establish `h1 : (t - 1) * A = A * (t - 1)` using `by rw [sub_mul, mul_sub, ht, one_mul, mul_one]`. Establish `h2 : A * (t - 1) * (A * (t' - 1)) = A * (t - 1) * (t' - 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_add, add_mul, add_mul, h2]`. Use `noncomm_ring`.
-/
theorem uu_mul {R : Type} [Ring R] (A t t' : R) (hA : A * A = A) (ht : t * A = A * t) :
    (1 + A * (t - 1)) * (1 + A * (t' - 1)) = 1 + A * (t * t' - 1) := by
  have h1 : (t - 1) * A = A * (t - 1) := by rw [sub_mul, mul_sub, ht, one_mul, mul_one]
  have h2 : A * (t - 1) * (A * (t' - 1)) = A * (t - 1) * (t' - 1) := by
    calc A * (t - 1) * (A * (t' - 1)) = A * ((t - 1) * A) * (t' - 1) := by simp only [mul_assoc]
      _ = (A * A) * (t - 1) * (t' - 1) := by rw [h1]; simp only [mul_assoc]
      _ = _ := by rw [hA]
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

/- English proof (translation)
Establish `h2 : A * x * (B * x) = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_add, add_mul, add_mul, h2]`. Use `noncomm_ring`.
-/
theorem uu_add {R : Type} [Ring R] (A B x : R) (hAB : A * B = 0) (hx : x * B = B * x) :
    (1 + A * x) * (1 + B * x) = 1 + (A + B) * x := by
  have h2 : A * x * (B * x) = 0 := by
    calc A * x * (B * x) = A * (x * B) * x := by simp only [mul_assoc]
      _ = (A * B) * x * x := by rw [hx]; simp only [mul_assoc]
      _ = 0 := by rw [hAB]; simp
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem rm_mul (a b : Matrix (Fin n) (Fin n) E) : rm (a * b) = rm a * rm b := Matrix.map_mul

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rm]`.
-/
theorem rm_add (a b : Matrix (Fin n) (Fin n) E) : rm (a + b) = rm a + rm b := by
  ext i j; simp [rm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rm]`.
-/
theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j; simp [rm]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv, mul_one]`. Use `_ = (t⁻¹ : GA E n).val * (t.val * rm e) * (t⁻¹ : GA E n).val := by`. Rewrite using `[ht]`. Simplify using `only [mul_assoc]`.

Use `_ = rm e * (t⁻¹ : GA E n).val := by rw [← mul_assoc, Units.inv_mul, one_mul]`.
-/
theorem comm_inv {e : Matrix (Fin n) (Fin n) E} {t : GA E n} (ht : t.val * rm e = rm e * t.val) :
    (t⁻¹ : GA E n).val * rm e = rm e * (t⁻¹ : GA E n).val := by
  calc (t⁻¹ : GA E n).val * rm e = (t⁻¹ : GA E n).val * (rm e * (t.val * (t⁻¹ : GA E n).val)) := by
        rw [Units.mul_inv, mul_one]
    _ = (t⁻¹ : GA E n).val * (t.val * rm e) * (t⁻¹ : GA E n).val := by
        rw [ht]; simp only [mul_assoc]
    _ = rm e * (t⁻¹ : GA E n).val := by rw [← mul_assoc, Units.inv_mul, one_mul]

/- English proof (translation)
Unfold `chi`. Rewrite using `[← Matrix.det_mul, uu_mul (rm e) t.val t'.val (by rw [← rm_mul, he]) ht, Units.val_mul]`.
-/
theorem chi_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n)
    (ht : t.val * rm e = rm e * t.val) : chi e (t * t') = chi e t * chi e t' := by
  unfold chi
  rw [← Matrix.det_mul, uu_mul (rm e) t.val t'.val (by rw [← rm_mul, he]) ht, Units.val_mul]

/- English proof (translation)
Simplify using `[chi]`.
-/
theorem chi_one (e : Matrix (Fin n) (Fin n) E) : chi e (1 : GA E n) = 1 := by
  simp [chi]

/- English proof (translation)
The claim follows from `IsUnit.of_mul_eq_one (chi e t⁻¹) (by rw [← chi_mul e he t _ ht, mul_inv_cancel, chi_one])`.
-/
theorem chi_isUnit (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n)
    (ht : t.val * rm e = rm e * t.val) : IsUnit (chi e t) :=
  IsUnit.of_mul_eq_one (chi e t⁻¹) (by rw [← chi_mul e he t _ ht, mul_inv_cancel, chi_one])

/- English proof (translation)
Unfold `lam`. Rewrite using `[chi_mul e he t t' ht]`. Conclude with `GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit e he t ht) (chi_isUnit e he t' ht')`.
-/
theorem lam_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n) (ht : t.val * rm e = rm e * t.val)
    (ht' : t'.val * rm e = rm e * t'.val) : lam e (t * t') = lam e t + lam e t' := by
  unfold lam
  rw [chi_mul e he t t' ht]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit e he t ht) (chi_isUnit e he t' ht')

/- English proof (translation)
Establish `h` using `lam_mul e he t t⁻¹ ht (comm_inv ht)`. Establish `h0 : lam e (1 : GA E n) = 0`. Rewrite using `[lam, chi_one, ← map_one (algebraMap E (Ad E))]`. Conclude with `GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero`. Rewrite `h` using `[mul_inv_cancel, h0]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lam_inv (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t.val * rm e = rm e * t.val) :
    lam e t⁻¹ = - lam e t := by
  have h := lam_mul e he t t⁻¹ ht (comm_inv ht)
  have h0 : lam e (1 : GA E n) = 0 := by
    rw [lam, chi_one, ← map_one (algebraMap E (Ad E))]
    exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero
  rw [mul_inv_cancel, h0] at h
  linarith

/- English proof (translation)
Establish `h1 : chi (0 : Matrix (Fin n) (Fin n) E) t = algebraMap E (Ad E) 1`. Simplify using `[chi, rm_zero]`. Rewrite using `[lam, h1]`. Conclude with `GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero`.
-/
theorem lam_zero (t : GA E n) : lam (0 : Matrix (Fin n) (Fin n) E) t = 0 := by
  have h1 : chi (0 : Matrix (Fin n) (Fin n) E) t = algebraMap E (Ad E) 1 := by
    simp [chi, rm_zero]
  rw [lam, h1]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero

/- English proof (translation)
Unfold `chi`. Establish `h1 : (t.val - 1) * rm b = rm b * (t.val - 1)` using `by rw [sub_mul, mul_sub, hb, one_mul, mul_one]`. Rewrite using `[← Matrix.det_mul, uu_add (rm a) (rm b) _ (by rw [← rm_mul, hab, rm_zero]) h1, rm_add]`.
-/
theorem chi_add (a b : Matrix (Fin n) (Fin n) E) (hab : a * b = 0) (t : GA E n)
    (hb : t.val * rm b = rm b * t.val) : chi (a + b) t = chi a t * chi b t := by
  unfold chi
  have h1 : (t.val - 1) * rm b = rm b * (t.val - 1) := by rw [sub_mul, mul_sub, hb, one_mul, mul_one]
  rw [← Matrix.det_mul, uu_add (rm a) (rm b) _ (by rw [← rm_mul, hab, rm_zero]) h1, rm_add]

/- English proof (translation)
Establish `key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i ∧ t.val * rm (∑ i ∈ s, f i) = rm (∑ i ∈ s, f i) * t.val ∧ lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [rm_zero, lam_zero]`. Consider the case `insert a s ha ih`. Take `⟨h1, h2, h3⟩` from `ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi j hj => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) (fun i hi => ht i (Finset.mem_insert_of_mem hi))`.

Establish `haa` using `hf a (Finset.mem_insert_self _ _)`. Establish `hta` using `ht a (Finset.mem_insert_self _ _)`. Establish `hl : f a * ∑ i ∈ s, f i = 0`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))`.

Establish `hr : (∑ i ∈ s, f i) * f a = 0`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_eq_zero fun i hi => ho i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _) (fun h => ha (h ▸ hi))`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_mul, mul_add, mul_add, hl, hr, haa, h1]`. Simplify using the standard rewrite rules. Rewrite using `[rm_add, mul_add, add_mul, hta, h2]`. Unfold `lam at h3 ⊢`. Rewrite using `[chi_add _ _ hl t h2, GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit _ haa t hta) (chi_isUnit _ h1 t h2), h3]`.

Conclude with `key.2.2`.
-/
theorem lam_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) E) (hf : ∀ i ∈ s, f i * f i = f i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (t : GA E n) (ht : ∀ i ∈ s, t.val * rm (f i) = rm (f i) * t.val) :
    lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
  classical
  have key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i ∧
      t.val * rm (∑ i ∈ s, f i) = rm (∑ i ∈ s, f i) * t.val ∧ lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
    induction s using Finset.induction_on with
    | empty => simp [rm_zero, lam_zero]
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (fun i hi => ht i (Finset.mem_insert_of_mem hi))
      have haa := hf a (Finset.mem_insert_self _ _)
      have hta := ht a (Finset.mem_insert_self _ _)
      have hl : f a * ∑ i ∈ s, f i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have hr : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun i hi => ho i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)
          (fun h => ha (h ▸ hi))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_mul, mul_add, mul_add, hl, hr, haa, h1]; simp
      · rw [rm_add, mul_add, add_mul, hta, h2]
      · unfold lam at h3 ⊢
        rw [chi_add _ _ hl t h2, GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit _ haa t hta) (chi_isUnit _ h1 t h2), h3]
  exact key.2.2

/- English proof (translation)
Establish `h1 : chi e (ratGL E n r) = algebraMap E (Ad E) (1 + e * (r.val - 1)).det`. Establish `: 1 + rm e * ((ratGL E n r).val - 1) = (1 + e * (r.val - 1)).map (algebraMap E (Ad E))`. Establish `h2 : (ratGL E n r).val = r.val.map (algebraMap E (Ad E))` using `rfl`. Rewrite using `[h2]`. Use extensionality with `i j`.

Simplify using `[rm, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, apply_ite, map_sum]`. Rewrite using `[chi, this]`. Conclude with `(RingHom.map_det _ _).symm`. Establish `h2` using `chi_isUnit e he _ hr`. Rewrite `h2` using `[h1]`.

Rewrite using `[lam, h1]`. Use `GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap _ fun h0 => ?_` and prove the remaining obligations. Rewrite `h2` using `[h0, map_zero]`. Take `⟨v⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Conclude with `(h2.map (cV v)).ne_zero (map_zero _)`.
-/
theorem lam_rat (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (r : GL (Fin n) E)
    (hr : (ratGL E n r).val * rm e = rm e * (ratGL E n r).val) : lam e (ratGL E n r) = 0 := by
  have h1 : chi e (ratGL E n r) = algebraMap E (Ad E) (1 + e * (r.val - 1)).det := by
    have : 1 + rm e * ((ratGL E n r).val - 1) = (1 + e * (r.val - 1)).map (algebraMap E (Ad E)) := by
      have h2 : (ratGL E n r).val = r.val.map (algebraMap E (Ad E)) := rfl
      rw [h2]
      ext i j
      simp [rm, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, apply_ite, map_sum]
    rw [chi, this]
    exact (RingHom.map_det _ _).symm
  have h2 := chi_isUnit e he _ hr
  rw [h1] at h2
  rw [lam, h1]
  refine GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap _ fun h0 => ?_
  rw [h0, map_zero] at h2
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (h2.map (cV v)).ne_zero (map_zero _)

end Chi

end GlobalTheory.CompanionTheory.TorusCh

end
