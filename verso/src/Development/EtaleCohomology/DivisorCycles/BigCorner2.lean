import Development.EtaleCohomology.DivisorCycles.CycleCount
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan

open Matrix

namespace LateralTheory.DivDb.BigCorner₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N n : ℕ}

def gens (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x | ∃ a ∈ A, ∃ g, x = a * (ρ g : Mat C N)}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma rmul (ρ : Γ →* GL (Fin N) C) (g h : Γ) : (ρ (g * h) : Mat C N) = ρ g * ρ h := by simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma rone (ρ : Γ →* GL (Fin N) C) : (ρ 1 : Mat C N) = 1 := by simp

/- English proof (translation)
Rewrite using `[← rmul, mul_inv_cancel, rone]`.
-/
lemma rinv (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g : Mat C N) * ρ g⁻¹ = 1 := by
  rw [← rmul, mul_inv_cancel, rone]

/- English proof (translation)
Rewrite using `[← rmul, inv_mul_cancel, rone]`.
-/
lemma rinv' (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g⁻¹ : Mat C N) * ρ g = 1 := by
  rw [← rmul, inv_mul_cancel, rone]

/- English proof (translation)
Take `⟨a, ha, g, rfl⟩` from `hx`. Take `⟨b, hb, h, rfl⟩` from `hy`. Use `⟨a * ((ρ g : Mat C N) * b * ρ g⁻¹), A.mul_mem ha (hN g b hb), g * h, ?_⟩` and prove the remaining obligations. Establish `key : (ρ g⁻¹ : Mat C N) * (ρ g * ρ h) = ρ h` using `by rw [← mul_assoc, rinv', one_mul]`. Rewrite using `[rmul]`.

Simplify using `only [mul_assoc, key]`.
-/
lemma gen_mul (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A)
    {x y : Mat C N} (hx : x ∈ gens ρ A) (hy : y ∈ gens ρ A) : x * y ∈ gens ρ A := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  obtain ⟨b, hb, h, rfl⟩ := hy
  refine ⟨a * ((ρ g : Mat C N) * b * ρ g⁻¹), A.mul_mem ha (hN g b hb), g * h, ?_⟩
  have key : (ρ g⁻¹ : Mat C N) * (ρ g * ρ h) = ρ h := by rw [← mul_assoc, rinv', one_mul]
  rw [rmul]; simp only [mul_assoc, key]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul ρ A hN x y hx hy`.
-/
lemma span_mul (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A)
    (x y : Mat C N) (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) :=
  _root_.UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul ρ A hN x y hx hy

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, A.one_mem, 1, by rw [rone, one_mul]⟩`.
-/
lemma one_mem_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) :
    (1 : Mat C N) ∈ Submodule.span C (gens ρ A) :=
  Submodule.subset_span ⟨1, A.one_mem, 1, by rw [rone, one_mul]⟩

noncomputable def RR (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) :
    Subalgebra C (Mat C N) :=
  (Submodule.span C (gens ρ A)).toSubalgebra (one_mem_span ρ A) (span_mul ρ A hN)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_RR {ρ : Γ →* GL (Fin N) C} {A : Subalgebra C (Mat C N)} {hN : Normd ρ A} {x : Mat C N} :
    x ∈ RR ρ A hN ↔ x ∈ Submodule.span C (gens ρ A) := Iff.rfl

/- English proof (translation)
Take `⟨a, ha, g, rfl⟩` from `hx`. Distinguish the cases in `h : p i * a * (ρ g : Mat C N) * p i = 0`. Conclude with `⟨0, by rw [zero_smul, ← mul_assoc, h]⟩`. Take `⟨w, hw, hpw⟩` from `hyp g i ⟨a, ha, h⟩`. Establish `ha' : (ρ g⁻¹ : Mat C N) * a * ρ g ∈ A` using `by simpa using hN g⁻¹ a ha`.

Establish `e1 : a * (ρ g : Mat C N) = ρ g * ((ρ g⁻¹ : Mat C N) * a * ρ g)`. Simplify using `only [← mul_assoc, rinv, one_mul]`. Take `⟨c, hc⟩` from `hC.2 _ (A.mul_mem hw ha') i`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, ← mul_assoc, ← mul_assoc, hpw, ← hc]`.

Simplify using `only [mul_assoc]`.
-/
lemma corner_gen (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ gens ρ A) : ∃ c : C, p i * x * p i = c • p i := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  by_cases h : p i * a * (ρ g : Mat C N) * p i = 0
  · exact ⟨0, by rw [zero_smul, ← mul_assoc, h]⟩
  · obtain ⟨w, hw, hpw⟩ := hyp g i ⟨a, ha, h⟩
    have ha' : (ρ g⁻¹ : Mat C N) * a * ρ g ∈ A := by simpa using hN g⁻¹ a ha
    have e1 : a * (ρ g : Mat C N) = ρ g * ((ρ g⁻¹ : Mat C N) * a * ρ g) := by
      simp only [← mul_assoc, rinv, one_mul]
    obtain ⟨c, hc⟩ := hC.2 _ (A.mul_mem hw ha') i
    refine ⟨c, ?_⟩
    rw [e1, ← mul_assoc, ← mul_assoc, hpw, ← hc]; simp only [mul_assoc]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx' => exact corner_gen ρ A p hC hN hyp i hx'`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨c, hc⟩` from `hu`.

Take `⟨d, hd⟩` from `hv`. Conclude with `⟨c + d, by rw [mul_add, add_mul, hc, hd, add_smul]⟩`. Consider the case `smul c u _ hu`. Take `⟨d, hd⟩` from `hu`. Conclude with `⟨c * d, by rw [mul_smul_comm, smul_mul_assoc, hd, smul_smul]⟩`.
-/
lemma corner_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∃ c : C, p i * x * p i = c • p i := by
  induction hx using Submodule.span_induction with
  | mem x hx' => exact corner_gen ρ A p hC hN hyp i hx'
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨c, hc⟩ := hu; obtain ⟨d, hd⟩ := hv
    exact ⟨c + d, by rw [mul_add, add_mul, hc, hd, add_smul]⟩
  | smul c u _ hu =>
    obtain ⟨d, hd⟩ := hu
    exact ⟨c * d, by rw [mul_smul_comm, smul_mul_assoc, hd, smul_smul]⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx'`. Take `⟨a, ha, h, rfl⟩` from `hx'`. Use `Submodule.subset_span ⟨(ρ g : Mat C N) * a * ρ g⁻¹, hN g a ha, g * h * g⁻¹, ?_⟩` and prove the remaining obligations. Establish `key : (ρ g⁻¹ : Mat C N) * (ρ g * (ρ h * ρ g⁻¹)) = ρ h * ρ g⁻¹`.

Rewrite using `[← mul_assoc, rinv', one_mul]`. Rewrite using `[rmul, rmul]`. Simplify using `only [mul_assoc, key]`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [mul_add, add_mul]`.

Conclude with `Submodule.add_mem _ hu hv`. Consider the case `smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hu`.
-/
lemma normd_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) (g : Γ)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) :
    (ρ g : Mat C N) * x * (ρ g⁻¹ : Mat C N) ∈ Submodule.span C (gens ρ A) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, h, rfl⟩ := hx'
    refine Submodule.subset_span ⟨(ρ g : Mat C N) * a * ρ g⁻¹, hN g a ha, g * h * g⁻¹, ?_⟩
    have key : (ρ g⁻¹ : Mat C N) * (ρ g * (ρ h * ρ g⁻¹)) = ρ h * ρ g⁻¹ := by
      rw [← mul_assoc, rinv', one_mul]
    rw [rmul, rmul]; simp only [mul_assoc, key]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hu

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx'`. Take `⟨a, ha, g, rfl⟩` from `hx'`. Introduce `v hv`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Conclude with `hK W hW a ha _ (hW g v hv)`. Consider the case `zero => intro v _`. Simplify using the standard rewrite rules. Consider the case `add u v _ _ hu hv => intro w hw`. Rewrite using `[Matrix.add_mulVec]`.

Conclude with `W.add_mem (hu w hw) (hv w hw)`. Consider the case `smul c u _ hu => intro w hw`. Rewrite using `[Matrix.smul_mulVec]`. Conclude with `W.smul_mem c (hu w hw)`.
-/
lemma keeps_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hK : Keeps ρ A)
    (W : Submodule C (Fin N → C)) (hW : ∀ g, ∀ v ∈ W, (ρ g : Mat C N) *ᵥ v ∈ W)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∀ v ∈ W, x *ᵥ v ∈ W := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, g, rfl⟩ := hx'
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    exact hK W hW a ha _ (hW g v hv)
  | zero => intro v _; simp
  | add u v _ _ hu hv => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hu w hw) (hv w hw)
  | smul c u _ hu => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hu w hw)

end LateralTheory.DivDb.BigCorner₂

open LateralTheory.DivDb.BigCorner₂ in
/- English proof (translation)
Introduce `Γ C _ _ N n ρ A p hC hN hK hyp`. Use `⟨RR ρ A hN, fun g => ?_, ⟨fun i => ?_, fun a ha i => ?_⟩, fun g a ha => ?_, fun W hW a ha => ?_⟩` and prove the remaining obligations. Conclude with `mem_RR.2 (Submodule.subset_span ⟨1, A.one_mem, g, (one_mul _).symm⟩)`. Conclude with `mem_RR.2 (Submodule.subset_span ⟨p i, hC.1 i, 1, by rw [rone, mul_one]⟩)`. Conclude with `corner_span ρ A p hC hN hyp i (mem_RR.1 ha)`.

Conclude with `mem_RR.2 (normd_span ρ A hN g (mem_RR.1 ha))`. Conclude with `keeps_span ρ A hK W hW (mem_RR.1 ha)`.
-/
theorem LateralTheory.DivDb.BigCorner₂.BigCorner_of : LateralTheory.DivDb.BigCorner := by
  intro Γ C _ _ N n ρ A p hC hN hK hyp
  refine ⟨RR ρ A hN, fun g => ?_, ⟨fun i => ?_, fun a ha i => ?_⟩, fun g a ha => ?_, fun W hW a ha => ?_⟩
  · exact mem_RR.2 (Submodule.subset_span ⟨1, A.one_mem, g, (one_mul _).symm⟩)
  · exact mem_RR.2 (Submodule.subset_span ⟨p i, hC.1 i, 1, by rw [rone, mul_one]⟩)
  · exact corner_span ρ A p hC hN hyp i (mem_RR.1 ha)
  · exact mem_RR.2 (normd_span ρ A hN g (mem_RR.1 ha))
  · exact keeps_span ρ A hK W hW (mem_RR.1 ha)
