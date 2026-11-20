import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensor

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

section Lift

variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
  [Algebra R B]

def tensorLift (u : A →+* C) (v : B →+* C) (h : u.comp (algebraMap R A) = v.comp (algebraMap R B)) :
    A ⊗[R] B →+* C :=
  letI : Algebra R C := (v.comp (algebraMap R B)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨u, fun r => by
        show u (algebraMap R A r) = v (algebraMap R B r)
        exact congrArg (fun w : R →+* C => w r) h⟩ : A →ₐ[R] C)
    (⟨v, fun _ => rfl⟩ : B →ₐ[R] C)).toRingHom

/- English proof (translation)
Simplify using `[tensorLift, Algebra.TensorProduct.productMap_apply_tmul]`.
-/
theorem tensorLift_tmul (u : A →+* C) (v : B →+* C)
    (h : u.comp (algebraMap R A) = v.comp (algebraMap R B)) (a : A) (b : B) :
    tensorLift u v h (a ⊗ₜ[R] b) = u a * v b := by
  simp [tensorLift, Algebra.TensorProduct.productMap_apply_tmul]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor`. Consider the case `exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor`. Consider the case `(apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor ..)`.
-/
theorem ringHom_ext {g h : A ⊗[R] B →+* C} (h1 : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (h2 : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  first
  | exact @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor
  | exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor
  | (apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor ..)

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem algebraMap_tmul_one (r : R) :
    (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Lift

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible S`. Take `⟨a, ha⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hs hϖ`. Take `⟨b, hb⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ`. Establish `hb1 : 1 ≤ b`. Break down `Nat.eq_zero_or_pos b with h | h` into its components or cases.

Substitute `h` using the available equality. Conclude with `absurd (hb.symm.isUnit (by simp)) hx`. Conclude with `h`. Use `⟨a, ha.dvd.trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_mul]`. Conclude with `pow_dvd_pow _ (Nat.le_mul_of_pos_left a hb1)`. Use `_ ∣ x ^ a := pow_dvd_pow_of_dvd hb.symm.dvd a`.
-/
theorem exists_dvd_pow {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {s x : S}
    (hs : s ≠ 0) (hx0 : x ≠ 0) (hx : ¬ IsUnit x) : ∃ n : ℕ, s ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs hϖ
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      exact absurd (hb.symm.isUnit (by simp)) hx
    · exact h
  refine ⟨a, ha.dvd.trans ?_⟩
  calc ϖ ^ a ∣ (ϖ ^ b) ^ a := by
        rw [← pow_mul]; exact pow_dvd_pow _ (Nat.le_mul_of_pos_left a hb1)
    _ ∣ x ^ a := pow_dvd_pow_of_dvd hb.symm.dvd a

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section FirstIso

variable {R₁ B₁ S₁ K₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [CommRing K₁]
  [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁] [Algebra S₁ K₁] [Algebra B DA]
  [Algebra B K₁] (β : B →+* B₁)

abbrev ov (b : B₁) : Over β := b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_bc (b : B₁) :
    algebraMap B₁ (BC β DA) b = ov β b ⊗ₜ[B] (1 : DA) := rfl

/- English proof (translation)
The claim follows from `algebraMap_tmul_one (A := Over β) b`.
-/
theorem tmul_one_bc (b : B) :
    ov β (β b) ⊗ₜ[B] (1 : DA) = (1 : Over β) ⊗ₜ[B] algebraMap B DA b :=
  algebraMap_tmul_one (A := Over β) b

def vE (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β) : BC β DA →+* K₁ ⊗[B] DA :=
  tensorLift (R := B) (A := Over β) (Algebra.TensorProduct.includeLeftRingHom.comp ι : B₁ →+* K₁ ⊗[B] DA)
    (Algebra.TensorProduct.includeRight : DA →ₐ[B] K₁ ⊗[B] DA).toRingHom (by
      apply RingHom.ext; intro b
      show ι (β b) ⊗ₜ[B] (1 : DA) = (1 : K₁) ⊗ₜ[B] algebraMap B DA b
      rw [← RingHom.comp_apply ι β, ← hBK]
      exact algebraMap_tmul_one b)

/- English proof (translation)
Unfold `vE`. Use `(tensorLift_tmul (R := B) (A := Over β) _ _ _ b d).trans ?_` and prove the remaining obligations. Use `show (ι b ⊗ₜ[B] (1 : DA)) * ((1 : K₁) ⊗ₜ[B] d) = _`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem vE_tmul (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β) (b : B₁) (d : DA) :
    vE β ι hBK (ov β b ⊗ₜ[B] d) = ι b ⊗ₜ[B] d := by
  unfold vE
  refine (tensorLift_tmul (R := B) (A := Over β) _ _ _ b d).trans ?_
  show (ι b ⊗ₜ[B] (1 : DA)) * ((1 : K₁) ⊗ₜ[B] d) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

def fwd₁ [Algebra R₁ (BC β DA)] (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁)) :
    S₁ ⊗[R₁] BC β DA →+* K₁ ⊗[B] DA :=
  tensorLift (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap S₁ K₁)) (vE β ι hBK) (by
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hD]
    simp only [RingHom.comp_apply]
    rw [algebraMap_bc, vE_tmul, ← RingHom.comp_apply ι, hι, RingHom.comp_apply]
    rfl)

/- English proof (translation)
Unfold `fwd₁`. Conclude with `tensorLift_tmul _ _ _ s z`.
-/
theorem fwd₁_tmul [Algebra R₁ (BC β DA)] (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁)) (s : S₁) (z : BC β DA) :
    fwd₁ β ι hBK hD hι (s ⊗ₜ[R₁] z) = (algebraMap S₁ K₁ s ⊗ₜ[B] (1 : DA)) * vE β ι hBK z := by
  unfold fwd₁
  exact tensorLift_tmul _ _ _ s z

def uT [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) :
    K₁ →+* S₁ ⊗[R₁] BC β DA :=
  IsLocalization.lift (M := nonZeroDivisors S₁) (g := Algebra.TensorProduct.includeLeftRingHom)
    (fun s => hunit s.1 s.2)

/- English proof (translation)
Unfold `uT`. Conclude with `IsLocalization.lift_eq _ _`.
-/
theorem uT_algebraMap [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) (s : S₁) :
    uT (K₁ := K₁) β hunit (algebraMap S₁ K₁ s) = s ⊗ₜ[R₁] (1 : BC β DA) := by
  unfold uT
  exact IsLocalization.lift_eq _ _

/- English proof (translation)
Apply `IsLocalization.ringHom_ext N` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← RingHom.comp_apply ι, hι, RingHom.comp_apply, uT_algebraMap, ← RingHom.comp_apply _ (algebraMap R₁ B₁), ← hD]`.

Conclude with `algebraMap_tmul_one r`.
-/
theorem uT_comp_ι [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) (ι : B₁ →+* K₁)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁))
    (N : Submonoid R₁) [IsLocalization N B₁] :
    (uT β hunit).comp ι =
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom.comp
        (algebraMap B₁ (BC β DA)) := by
  apply IsLocalization.ringHom_ext N
  apply RingHom.ext; intro r
  simp only [RingHom.comp_apply]
  rw [← RingHom.comp_apply ι, hι, RingHom.comp_apply, uT_algebraMap, ← RingHom.comp_apply _ (algebraMap R₁ B₁), ← hD]
  exact algebraMap_tmul_one r

end FirstIso

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section FirstIso2

variable {R₁ B₁ S₁ K₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [CommRing K₁]
  [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁] [Algebra S₁ K₁] [Algebra B DA]
  [Algebra B K₁] (β : B →+* B₁) [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
  (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
  (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
  (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁))
  (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA)))
  (N : Submonoid R₁) [IsLocalization N B₁]

def bwd₁ : K₁ ⊗[B] DA →+* S₁ ⊗[R₁] BC β DA :=
  tensorLift (R := B) (uT β hunit)
    ((Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom.comp
      (Algebra.TensorProduct.includeRight : DA →ₐ[B] BC β DA).toRingHom) (by
    apply RingHom.ext; intro b
    rw [RingHom.comp_apply, hBK, RingHom.comp_apply, ← RingHom.comp_apply (uT β hunit) ι,
      uT_comp_ι β hunit ι hD hι N]
    show (1 : S₁) ⊗ₜ[R₁] (algebraMap B₁ (BC β DA) (β b)) =
      (1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] algebraMap B DA b)
    rw [algebraMap_bc, tmul_one_bc])

omit [IsFractionRing S₁ K₁] [Algebra S₁ K₁] [Algebra B K₁] in
/- English proof (translation)
Rewrite using `[← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def]`.
-/
theorem one_tmul_one_bc : ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] (1 : DA)) : S₁ ⊗[R₁] BC β DA) = 1 := by
  rw [← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def]

/- English proof (translation)
Unfold `bwd₁`. Conclude with `tensorLift_tmul _ _ _ k d`.
-/
theorem bwd₁_tmul (k : K₁) (d : DA) :
    bwd₁ β ι hBK hD hι hunit N (k ⊗ₜ[B] d) =
      uT β hunit k * ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] d)) := by
  unfold bwd₁
  exact tensorLift_tmul _ _ _ k d

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors S₁)` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `s`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, uT_algebraMap, fwd₁_tmul, map_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem fwd₁_comp_uT :
    (fwd₁ β ι hBK hD hι).comp (uT β hunit) = Algebra.TensorProduct.includeLeftRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors S₁)
  apply RingHom.ext; intro s
  rw [RingHom.comp_apply, RingHom.comp_apply, uT_algebraMap, fwd₁_tmul, map_one, mul_one]
  rfl

/- English proof (translation)
Apply `ringHom_ext (A := Over β)` to reduce the goal to its premises. Introduce `(a : B₁)`. Express the relevant statement in the definitionally equal form `(bwd₁ β ι hBK hD hι hunit N) ((vE β ι hBK) (ov β a ⊗ₜ[B] (1 : DA))) = _`. Rewrite using `[vE_tmul, bwd₁_tmul, ← RingHom.comp_apply (uT β hunit) ι, uT_comp_ι β hunit ι hD hι N]`. Use `show (1 : S₁) ⊗ₜ[R₁] (algebraMap B₁ (BC β DA) a) * ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] (1 : DA))) = _`.

Rewrite using `[algebraMap_bc]`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Introduce `d`. Rewrite using `[RingHom.comp_apply, show (1 : Over β) = ov β 1 from rfl, vE_tmul, map_one, bwd₁_tmul, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem bwd₁_comp_vE :
    (bwd₁ β ι hBK hD hι hunit N).comp (vE β ι hBK) =
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom := by
  apply ringHom_ext (A := Over β)
  · intro (a : B₁)
    change (bwd₁ β ι hBK hD hι hunit N) ((vE β ι hBK) (ov β a ⊗ₜ[B] (1 : DA))) = _
    rw [vE_tmul, bwd₁_tmul, ← RingHom.comp_apply (uT β hunit) ι,
      uT_comp_ι β hunit ι hD hι N]
    show (1 : S₁) ⊗ₜ[R₁] (algebraMap B₁ (BC β DA) a) * ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] (1 : DA))) = _
    rw [algebraMap_bc]
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  · intro d
    rw [RingHom.comp_apply, show (1 : Over β) = ov β 1 from rfl, vE_tmul, map_one, bwd₁_tmul, map_one, one_mul]
    rfl

def equiv₁ : S₁ ⊗[R₁] BC β DA ≃+* K₁ ⊗[B] DA :=
  RingEquiv.ofRingHom (fwd₁ β ι hBK hD hι) (bwd₁ β ι hBK hD hι hunit N) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, bwd₁_tmul, one_tmul_one_bc, mul_one,
        ← RingHom.comp_apply, fwd₁_comp_uT]
      rfl
    · intro d
      rw [RingHom.comp_apply, bwd₁_tmul, map_one, one_mul, fwd₁_tmul, map_one,
        show (1 : Over β) = ov β 1 from rfl, vE_tmul, map_one]
      simp [Algebra.TensorProduct.tmul_mul_tmul]) (by
    apply ringHom_ext
    · intro s
      rw [RingHom.comp_apply, fwd₁_tmul, map_one, mul_one, bwd₁_tmul, one_tmul_one_bc, mul_one,
        uT_algebraMap]
      rfl
    · intro z
      rw [RingHom.comp_apply, fwd₁_tmul, map_one, ← Algebra.TensorProduct.one_def, one_mul,
        ← RingHom.comp_apply, bwd₁_comp_vE]
      rfl)

/- English proof (translation)
Use `show fwd₁ β ι hBK hD hι (s ⊗ₜ[R₁] (1 : BC β DA)) = _`. Rewrite using `[fwd₁_tmul, map_one, mul_one]`.
-/
theorem equiv₁_tmul_one (s : S₁) :
    equiv₁ β ι hBK hD hι hunit N (s ⊗ₜ[R₁] (1 : BC β DA)) = algebraMap S₁ K₁ s ⊗ₜ[B] (1 : DA) := by
  show fwd₁ β ι hBK hD hι (s ⊗ₜ[R₁] (1 : BC β DA)) = _
  rw [fwd₁_tmul, map_one, mul_one]

end FirstIso2

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section SecondIso

variable {K K₁ B DA : Type} [CommRing K] [CommRing K₁] [CommRing B] [CommRing DA] [Algebra K K₁]
  [Algebra B DA] [Algebra B K₁] (γ : B →+* K) (hBK : algebraMap B K₁ = (algebraMap K K₁).comp γ)

def fwd₂ : K₁ ⊗[K] BC γ DA →+* K₁ ⊗[B] DA :=
  tensorLift Algebra.TensorProduct.includeLeftRingHom (vE γ (algebraMap K K₁) hBK) (by
    apply RingHom.ext; intro k
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_bc, vE_tmul]
    rfl)

/- English proof (translation)
Unfold `fwd₂`. Conclude with `tensorLift_tmul _ _ _ a z`.
-/
theorem fwd₂_tmul (a : K₁) (z : BC γ DA) :
    fwd₂ γ hBK (a ⊗ₜ[K] z) = (a ⊗ₜ[B] (1 : DA)) * vE γ (algebraMap K K₁) hBK z := by
  unfold fwd₂
  exact tensorLift_tmul _ _ _ a z

def bwd₂ : K₁ ⊗[B] DA →+* K₁ ⊗[K] BC γ DA :=
  tensorLift (R := B) Algebra.TensorProduct.includeLeftRingHom
    ((Algebra.TensorProduct.includeRight : BC γ DA →ₐ[K] K₁ ⊗[K] BC γ DA).toRingHom.comp
      (Algebra.TensorProduct.includeRight : DA →ₐ[B] BC γ DA).toRingHom) (by
    apply RingHom.ext; intro b
    rw [RingHom.comp_apply, hBK, RingHom.comp_apply]
    show algebraMap K K₁ (γ b) ⊗ₜ[K] (1 : BC γ DA) = (1 : K₁) ⊗ₜ[K] ((1 : Over γ) ⊗ₜ[B] algebraMap B DA b)
    rw [algebraMap_tmul_one, algebraMap_bc, tmul_one_bc])

/- English proof (translation)
Unfold `bwd₂`. Conclude with `tensorLift_tmul _ _ _ a d`.
-/
theorem bwd₂_tmul (a : K₁) (d : DA) :
    bwd₂ γ hBK (a ⊗ₜ[B] d) = (a ⊗ₜ[K] (1 : BC γ DA)) * ((1 : K₁) ⊗ₜ[K] ((1 : Over γ) ⊗ₜ[B] d)) := by
  unfold bwd₂
  exact tensorLift_tmul _ _ _ a d

/- English proof (translation)
Apply `ringHom_ext (A := Over γ)` to reduce the goal to its premises. Introduce `(a : K)`. Express the relevant statement in the definitionally equal form `(bwd₂ γ hBK) ((vE γ (algebraMap K K₁) hBK) (ov γ a ⊗ₜ[B] (1 : DA))) = _`. Rewrite using `[vE_tmul, bwd₂_tmul, one_tmul_one_bc, mul_one, algebraMap_tmul_one, algebraMap_bc]`. Both sides reduce to the same expression.

Introduce `d`. Rewrite using `[RingHom.comp_apply, show (1 : Over γ) = ov γ 1 from rfl, vE_tmul, map_one, bwd₂_tmul, ← Algebra.TensorProduct.one_def, one_mul]`. Both sides reduce to the same expression.
-/
theorem bwd₂_comp_vE :
    (bwd₂ γ hBK).comp (vE γ (algebraMap K K₁) hBK) =
      (Algebra.TensorProduct.includeRight : BC γ DA →ₐ[K] K₁ ⊗[K] BC γ DA).toRingHom := by
  apply ringHom_ext (A := Over γ)
  · intro (a : K)
    change (bwd₂ γ hBK) ((vE γ (algebraMap K K₁) hBK) (ov γ a ⊗ₜ[B] (1 : DA))) = _
    rw [vE_tmul, bwd₂_tmul, one_tmul_one_bc, mul_one, algebraMap_tmul_one, algebraMap_bc]
    rfl
  · intro d
    rw [RingHom.comp_apply, show (1 : Over γ) = ov γ 1 from rfl, vE_tmul, map_one, bwd₂_tmul,
      ← Algebra.TensorProduct.one_def, one_mul]
    rfl

def equiv₂ : K₁ ⊗[K] BC γ DA ≃+* K₁ ⊗[B] DA :=
  RingEquiv.ofRingHom (fwd₂ γ hBK) (bwd₂ γ hBK) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, bwd₂_tmul, one_tmul_one_bc, mul_one, fwd₂_tmul, map_one, mul_one]
      rfl
    · intro d
      rw [RingHom.comp_apply, bwd₂_tmul, ← Algebra.TensorProduct.one_def, one_mul, fwd₂_tmul,
        show (1 : Over γ) = ov γ 1 from rfl, vE_tmul, map_one]
      simp [Algebra.TensorProduct.tmul_mul_tmul]) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, fwd₂_tmul, map_one, mul_one, bwd₂_tmul, one_tmul_one_bc, mul_one]
      rfl
    · intro z
      rw [RingHom.comp_apply, fwd₂_tmul, ← Algebra.TensorProduct.one_def, one_mul,
        ← RingHom.comp_apply, bwd₂_comp_vE]
      rfl)

/- English proof (translation)
Use `show bwd₂ γ hBK (a ⊗ₜ[B] (1 : DA)) = _`. Rewrite using `[bwd₂_tmul, one_tmul_one_bc, mul_one]`.
-/
theorem equiv₂_symm_tmul_one (a : K₁) :
    (equiv₂ γ hBK).symm (a ⊗ₜ[B] (1 : DA)) = a ⊗ₜ[K] (1 : BC γ DA) := by
  show bwd₂ γ hBK (a ⊗ₜ[B] (1 : DA)) = _
  rw [bwd₂_tmul, one_tmul_one_bc, mul_one]

end SecondIso

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

/- English proof (translation)
Introduce `s hs`. Take `⟨n, hn⟩` from `exists_dvd_pow (nonZeroDivisors.ne_zero hs) hx0 hxu`. Establish `hu : IsUnit ((algebraMap R₁ S₁ x) ⊗ₜ[R₁] (1 : BC β DA))`. Rewrite using `[algebraMap_tmul_one, hD, RingHom.comp_apply]`. Conclude with `(hxB.map (algebraMap B₁ (BC β DA))).map (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA)`.

Establish `h` using `map_dvd (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[R₁] BC β DA) hn`. Rewrite `h` using `[map_pow]`. Conclude with `isUnit_of_dvd_unit h (hu.pow n)`.
-/
theorem isUnit_tmul_one {R₁ B₁ S₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [IsDomain S₁]
    [IsDiscreteValuationRing S₁] [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁]
    [Algebra B DA] (β : B →+* B₁) [Algebra R₁ (BC β DA)]
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (x : R₁) (hx0 : algebraMap R₁ S₁ x ≠ 0) (hxu : ¬ IsUnit (algebraMap R₁ S₁ x))
    (hxB : IsUnit (algebraMap R₁ B₁ x)) :
    ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA)) := by
  intro s hs
  obtain ⟨n, hn⟩ := exists_dvd_pow (nonZeroDivisors.ne_zero hs) hx0 hxu
  have hu : IsUnit ((algebraMap R₁ S₁ x) ⊗ₜ[R₁] (1 : BC β DA)) := by
    rw [algebraMap_tmul_one, hD, RingHom.comp_apply]
    exact (hxB.map (algebraMap B₁ (BC β DA))).map
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA)
  have h := map_dvd (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[R₁] BC β DA) hn
  rw [map_pow] at h
  exact isUnit_of_dvd_unit h (hu.pow n)

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

/- English proof (translation)
Use `haveI : FaithfulSMul S (FractionRing S₁) := by`. Use `(faithfulSMul_iff_algebraMap_injective _ _).2 ?_` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_eq S S₁ (FractionRing S₁)]`. Conclude with `(IsFractionRing.injective S₁ (FractionRing S₁)).comp hSS₁`. Use `letI algKK₁ : Algebra (FractionRing S) (FractionRing S₁) := FractionRing.liftAlgebra S (FractionRing S₁)`.

Use `haveI : IsScalarTower S (FractionRing S) (FractionRing S₁) := FractionRing.isScalarTower_liftAlgebra _ _`. Set `γ : GlobalTheory.LocAcyc.GenFib A R →+* FractionRing S` to `IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (g := (algebraMap S (FractionRing S)).comp (algebraMap R S)) (by`. Introduce and unpack `⟨_, a, ha, rfl⟩`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Introduce `h`. Establish `h1` using `(injective_iff_map_eq_zero _).1 (IsFractionRing.injective S (FractionRing S)) _ h`. Establish `h2` using `(injective_iff_map_eq_zero _).1 hRS _ h1`. Establish `h3` using `(injective_iff_map_eq_zero _).1 hAR _ h2`. Conclude with `nonZeroDivisors.ne_zero ha h3)`.

Set `ι : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing S₁` to `IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) (g := (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁)) (by`. Introduce and unpack `⟨_, a, ha, rfl⟩`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Introduce `h`.

Establish `h1` using `(injective_iff_map_eq_zero _).1 (IsFractionRing.injective S₁ (FractionRing S₁)) _ h`. Establish `h2` using `(injective_iff_map_eq_zero _).1 hR₁S₁ _ h1`. Establish `h3` using `(injective_iff_map_eq_zero _).1 hAR₁ _ h2`. Conclude with `nonZeroDivisors.ne_zero ha h3)`. Establish `hι : ι.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁)` using `IsLocalization.lift_comp _`.

Use `letI algBK₁ : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) := ((algebraMap (FractionRing S) (FractionRing S₁)).comp γ).toAlgebra`. Establish `hBK₂ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) = (algebraMap (FractionRing S) (FractionRing S₁)).comp γ` using `rfl`. Establish `hBK₁ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) = ι.comp β`. Apply `IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Rewrite using `[hBK₂, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← RingHom.comp_apply β, hβ, RingHom.comp_apply]`. Establish `e1 : γ (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r) = algebraMap S (FractionRing S) (algebraMap R S r)` using `IsLocalization.lift_eq _ _`. Establish `e2 : ι (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ r)) = algebraMap S₁ (FractionRing S₁) (algebraMap R₁ S₁ (φ r))` using `IsLocalization.lift_eq _ _`. Rewrite using `[e1, e2, ← IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing S₁), IsScalarTower.algebraMap_apply S S₁ (FractionRing S₁), hloc]`.

Use `letI algD : Algebra R₁ (BC β DA) := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (BC β DA)).toAlgebra`. Establish `hD : algebraMap R₁ (BC β DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) (BC β DA)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁))` using `rfl`. Establish `hunit` using `isUnit_tmul_one (S₁ := S₁) β hD x hx0 hxu hxB`. Set `e₁` to `equiv₁ β ι hBK₁ hD hι hunit (Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))`. Set `e₂` to `equiv₂ (K₁ := FractionRing S₁) (DA := DA) γ hBK₂`.

Set `e : (S₁ ⊗[R₁] BC β DA) ≃ₐ[S₁] (FractionRing S₁ ⊗[FractionRing S] BC γ DA)` to `AlgEquiv.ofRingEquiv (f := e₁.trans e₂.symm) (fun s => by`. Rewrite using `[RingEquiv.trans_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, equiv₁_tmul_one, equiv₂_symm_tmul_one, Algebra.TensorProduct.algebraMap_apply])`. Establish `hE` using `H S S₁ (FractionRing S) (FractionRing S₁) hSS₁ q hq hqS ϖ hϖ y hy (BC γ DA) (bcAct γ DA q act) (isZTorsor_bc γ DA q hq act htor)`. Conclude with `Algebra.Etale.of_equiv (AlgEquiv.mapIntegralClosure e.symm)`.
-/
theorem etale_closure_core
    (H : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
      [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
      [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
      [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
      Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
      ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
      ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
      GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
      Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)))
    (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
    (hAR : Function.Injective (algebraMap A R))
    (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁]
    (hAR₁ : Function.Injective (algebraMap A₁ R₁)) (φ : R →+* R₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁)
    (hβ : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ)
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)) (hq : 0 < q)
    (htor : GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act)
    (S S₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁] [IsDomain S₁]
    [IsDiscreteValuationRing S₁] [Algebra R S] [Algebra R₁ S₁] [Algebra S S₁]
    (hRS : Function.Injective (algebraMap R S)) (hR₁S₁ : Function.Injective (algebraMap R₁ S₁))
    (hloc : ∀ r : R, algebraMap S S₁ (algebraMap R S r) = algebraMap R₁ S₁ (φ r))
    (hSS₁ : Function.Injective (algebraMap S S₁)) (hqS : IsUnit (q : S))
    (ϖ : S) (hϖ : Irreducible ϖ) (y : S₁) (hy : y ^ q = algebraMap S S₁ ϖ)
    (x : R₁) (hx0 : algebraMap R₁ S₁ x ≠ 0) (hxu : ¬ IsUnit (algebraMap R₁ S₁ x))
    (hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) x)) :
    letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (BC β DA)).toAlgebra
    Algebra.Etale S₁ (integralClosure S₁ (S₁ ⊗[R₁] BC β DA)) := by
  haveI : FaithfulSMul S (FractionRing S₁) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ?_
    rw [IsScalarTower.algebraMap_eq S S₁ (FractionRing S₁)]
    exact (IsFractionRing.injective S₁ (FractionRing S₁)).comp hSS₁
  letI algKK₁ : Algebra (FractionRing S) (FractionRing S₁) := FractionRing.liftAlgebra S (FractionRing S₁)
  haveI : IsScalarTower S (FractionRing S) (FractionRing S₁) := FractionRing.isScalarTower_liftAlgebra _ _
  let γ : GlobalTheory.LocAcyc.GenFib A R →+* FractionRing S :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      (g := (algebraMap S (FractionRing S)).comp (algebraMap R S)) (by
      rintro ⟨_, a, ha, rfl⟩
      refine isUnit_iff_ne_zero.2 ?_
      simp only [RingHom.comp_apply]
      intro h
      have h1 := (injective_iff_map_eq_zero _).1 (IsFractionRing.injective S (FractionRing S)) _ h
      have h2 := (injective_iff_map_eq_zero _).1 hRS _ h1
      have h3 := (injective_iff_map_eq_zero _).1 hAR _ h2
      exact nonZeroDivisors.ne_zero ha h3)
  let ι : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing S₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
      (g := (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁)) (by
      rintro ⟨_, a, ha, rfl⟩
      refine isUnit_iff_ne_zero.2 ?_
      simp only [RingHom.comp_apply]
      intro h
      have h1 := (injective_iff_map_eq_zero _).1 (IsFractionRing.injective S₁ (FractionRing S₁)) _ h
      have h2 := (injective_iff_map_eq_zero _).1 hR₁S₁ _ h1
      have h3 := (injective_iff_map_eq_zero _).1 hAR₁ _ h2
      exact nonZeroDivisors.ne_zero ha h3)
  have hι : ι.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁) := IsLocalization.lift_comp _
  letI algBK₁ : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) :=
    ((algebraMap (FractionRing S) (FractionRing S₁)).comp γ).toAlgebra
  have hBK₂ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) =
      (algebraMap (FractionRing S) (FractionRing S₁)).comp γ := rfl
  have hBK₁ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) = ι.comp β := by
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [hBK₂, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ← RingHom.comp_apply β, hβ, RingHom.comp_apply]
    have e1 : γ (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r) =
        algebraMap S (FractionRing S) (algebraMap R S r) := IsLocalization.lift_eq _ _
    have e2 : ι (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ r)) =
        algebraMap S₁ (FractionRing S₁) (algebraMap R₁ S₁ (φ r)) := IsLocalization.lift_eq _ _
    rw [e1, e2, ← IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing S₁),
      IsScalarTower.algebraMap_apply S S₁ (FractionRing S₁), hloc]
  letI algD : Algebra R₁ (BC β DA) := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (BC β DA)).toAlgebra
  have hD : algebraMap R₁ (BC β DA) =
      (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) (BC β DA)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) := rfl
  have hunit := isUnit_tmul_one (S₁ := S₁) β hD x hx0 hxu hxB
  let e₁ := equiv₁ β ι hBK₁ hD hι hunit (Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let e₂ := equiv₂ (K₁ := FractionRing S₁) (DA := DA) γ hBK₂
  let e : (S₁ ⊗[R₁] BC β DA) ≃ₐ[S₁] (FractionRing S₁ ⊗[FractionRing S] BC γ DA) :=
    AlgEquiv.ofRingEquiv (f := e₁.trans e₂.symm) (fun s => by
      rw [RingEquiv.trans_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, equiv₁_tmul_one, equiv₂_symm_tmul_one, Algebra.TensorProduct.algebraMap_apply])
  have hE := H S S₁ (FractionRing S) (FractionRing S₁) hSS₁ q hq hqS ϖ hϖ y hy
    (BC γ DA) (bcAct γ DA q act) (isZTorsor_bc γ DA q hq act htor)
  exact Algebra.Etale.of_equiv (AlgEquiv.mapIntegralClosure e.symm)

end GlobalTheory.KeyOriginTransport
