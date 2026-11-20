import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetConjOnMatricesKillingIntoSubspaceStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagModulus

section Linear

variable {K A B C : Type} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/- English proof (translation)
Establish `hb : b = (e : A →ₗ[K] B) ∘ₗ a ∘ₗ (e.symm : B →ₗ[K] A)`. Use extensionality with `x`. Simplify using `[h]`. Rewrite using `[hb, LinearMap.det_conj]`.
-/
theorem det_eq_of_intertwine (e : A ≃ₗ[K] B) (a : A →ₗ[K] A) (b : B →ₗ[K] B)
    (h : ∀ x, e (a x) = b (e x)) : LinearMap.det b = LinearMap.det a := by
  have hb : b = (e : A →ₗ[K] B) ∘ₗ a ∘ₗ (e.symm : B →ₗ[K] A) := by
    ext x
    simp [h]
  rw [hb, LinearMap.det_conj]

/- English proof (translation)
Establish `hle : LinearMap.ker π ≤ (LinearMap.ker π).comap b`. Introduce `x hx`. Rewrite `*` using `[Submodule.mem_comap, LinearMap.mem_ker]`. Rewrite using `[hc, hx, map_zero]`. Rewrite using `[LinearMap.det_eq_det_mul_det (LinearMap.ker π) b hle]`.

Use `congr 1`. Use `det_eq_of_intertwine ((LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)) a _ ?_` and prove the remaining obligations. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ha]`.

Use `(det_eq_of_intertwine (π.quotKerEquivOfSurjective hπ) _ c ?_).symm` and prove the remaining obligations. Introduce `x`. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ x`. Simplify using `[hc]`.
-/
theorem det_exact [FiniteDimensional K B] (i : A →ₗ[K] B) (π : B →ₗ[K] C)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π)
    (a : A →ₗ[K] A) (b : B →ₗ[K] B) (c : C →ₗ[K] C)
    (ha : ∀ x, i (a x) = b (i x)) (hc : ∀ x, π (b x) = c (π x)) :
    LinearMap.det b = LinearMap.det a * LinearMap.det c := by
  have hle : LinearMap.ker π ≤ (LinearMap.ker π).comap b := by
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker] at *
    rw [hc, hx, map_zero]
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker π) b hle]
  congr 1
  · refine det_eq_of_intertwine ((LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)) a _ ?_
    intro x
    apply Subtype.ext
    simp [ha]
  · refine (det_eq_of_intertwine (π.quotKerEquivOfSurjective hπ) _ c ?_).symm
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    simp [hc]

/- English proof (translation)
Substitute `hS hI` using the available equality. Set `i : ↥(P ⊓ Q) →ₗ[K] ↥P × ↥Q` to `LinearMap.prod (Submodule.inclusion inf_le_left) (-Submodule.inclusion inf_le_right)`. Set `π : ↥P × ↥Q →ₗ[K] ↥(P ⊔ Q)` to `LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)`. Establish `hi : Function.Injective i`. Introduce `x y hxy`.

Use `congrArg (fun z => ((z.1 : ↥P) : B)) hxy` as an intermediate fact. Conclude with `Subtype.ext (by simpa [i] using this)`. Establish `hπ : Function.Surjective π`. Introduce and unpack `⟨x, hx⟩`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`.

Conclude with `⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext (by simp [π])⟩`. Establish `hex : LinearMap.range i = LinearMap.ker π`. Use extensionality with `⟨p, q⟩`. Simplify using `only [LinearMap.mem_range, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx⟩`. Rewrite using `[← hx]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[i, π]`. Introduce `h`.

Establish `h' : (p : B) + q = 0` using `by simpa [π] using congrArg Subtype.val h`. Establish `hpQ : (p : B) ∈ Q`. Rewrite using `[eq_neg_of_add_eq_zero_left h']`. Conclude with `Q.neg_mem q.2`. Establish `hq : -(p : B) = q`.

Rewrite using `[neg_eq_iff_add_eq_zero]`. Conclude with `h'`. Use `⟨⟨p, Submodule.mem_inf.2 ⟨p.2, hpQ⟩⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)⟩` and prove the remaining obligations. Simplify `hq` using `[i]`. Establish `key` using `det_exact i π hi hπ hex (Φ.restrict hI') (LinearMap.prodMap (Φ.restrict hP') (Φ.restrict hQ')) (Φ.restrict hS') (fun x => Prod.ext (Subtype.ext (by simp [i])) (Subtype.ext (by simp [i]))) (fun x => Subtype.ext (by simp [π]))`.

Rewrite `key` using `[LinearMap.det_prodMap]`. Conclude with `key.symm`.
-/
theorem det_sup_mul_det_inf [FiniteDimensional K B] (Φ : B →ₗ[K] B) (P Q S I : Submodule K B)
    (hS : S = P ⊔ Q) (hI : I = P ⊓ Q)
    (hP' : ∀ x ∈ P, Φ x ∈ P) (hQ' : ∀ x ∈ Q, Φ x ∈ Q) (hS' : ∀ x ∈ S, Φ x ∈ S)
    (hI' : ∀ x ∈ I, Φ x ∈ I) :
    LinearMap.det (Φ.restrict hI') * LinearMap.det (Φ.restrict hS') =
      LinearMap.det (Φ.restrict hP') * LinearMap.det (Φ.restrict hQ') := by
  subst hS hI
  let i : ↥(P ⊓ Q) →ₗ[K] ↥P × ↥Q :=
    LinearMap.prod (Submodule.inclusion inf_le_left) (-Submodule.inclusion inf_le_right)
  let π : ↥P × ↥Q →ₗ[K] ↥(P ⊔ Q) :=
    LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hi : Function.Injective i := by
    intro x y hxy
    have := congrArg (fun z => ((z.1 : ↥P) : B)) hxy
    exact Subtype.ext (by simpa [i] using this)
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext (by simp [π])⟩
  have hex : LinearMap.range i = LinearMap.ker π := by
    ext ⟨p, q⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      apply Subtype.ext
      simp [i, π]
    · intro h
      have h' : (p : B) + q = 0 := by simpa [π] using congrArg Subtype.val h
      have hpQ : (p : B) ∈ Q := by
        rw [eq_neg_of_add_eq_zero_left h']
        exact Q.neg_mem q.2
      have hq : -(p : B) = q := by
        rw [neg_eq_iff_add_eq_zero]
        exact h'
      refine ⟨⟨p, Submodule.mem_inf.2 ⟨p.2, hpQ⟩⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)⟩
      simpa [i] using hq
  have key := det_exact i π hi hπ hex (Φ.restrict hI')
    (LinearMap.prodMap (Φ.restrict hP') (Φ.restrict hQ')) (Φ.restrict hS')
    (fun x => Prod.ext (Subtype.ext (by simp [i])) (Subtype.ext (by simp [i])))
    (fun x => Subtype.ext (by simp [π]))
  rw [LinearMap.det_prodMap] at key
  exact key.symm

end Linear

variable {n : ℕ}

def homSub (P Q : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q}
  add_mem' := fun {X Y} hX hY => ⟨fun y hy => by rw [Matrix.add_mulVec, hX.1 y hy, hY.1 y hy, add_zero],
    fun y => by rw [Matrix.add_mulVec]; exact Q.add_mem (hX.2 y) (hY.2 y)⟩
  zero_mem' := ⟨fun y _ => Matrix.zero_mulVec y, fun y => by rw [Matrix.zero_mulVec]; exact Q.zero_mem⟩
  smul_mem' := fun c X hX => ⟨fun y hy => by rw [Matrix.smul_mulVec, hX.1 y hy, smul_zero],
    fun y => by rw [Matrix.smul_mulVec]; exact Q.smul_mem c (hX.2 y)⟩

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_homSub {P Q : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ homSub P Q ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q := by
  exact Iff.rfl

def twoSided (f g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.mulRight ℂ g).comp (LinearMap.mulLeft ℂ f)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twoSided_apply (f g X : Matrix (Fin n) (Fin n) ℂ) : twoSided f g X = f * X * g := rfl

/- English proof (translation)
Rewrite using `[twoSided_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem twoSided_mulVec (f g X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    twoSided f g X *ᵥ y = f *ᵥ (X *ᵥ (g *ᵥ y)) := by
  rw [twoSided_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Introduce `X hX`. Rewrite `hX`, the goal using `[mem_homSub]`. Use `⟨fun y hy => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[twoSided_mulVec, hX.1 _ (hP y hy), Matrix.mulVec_zero]`. Rewrite using `[twoSided_mulVec]`.

Conclude with `hQ _ (hX.2 _)`.
-/
theorem homSub_stable {f g : Matrix (Fin n) (Fin n) ℂ} {P Q : Submodule ℂ (Fin n → ℂ)}
    (hP : ∀ y ∈ P, g *ᵥ y ∈ P) (hQ : ∀ y ∈ Q, f *ᵥ y ∈ Q) :
    ∀ X ∈ homSub P Q, twoSided f g X ∈ homSub P Q := by
  intro X hX
  rw [mem_homSub] at hX ⊢
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [twoSided_mulVec, hX.1 _ (hP y hy), Matrix.mulVec_zero]
  · rw [twoSided_mulVec]
    exact hQ _ (hX.2 _)

/- English proof (translation)
Establish `hf : ∀ y ∈ V, Matrix.toLin' f y ∈ V` using `fun y hy => by`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `hV y hy`. Establish `hg : ∀ y ∈ V, Matrix.toLin' g y ∈ V` using `fun y hy => by`. Rewrite using `[Matrix.toLin'_apply]`.

Conclude with `GlobalTheory.FlagLeviGroup.inv_keeps hgf V hV y hy`. Unfold `detOn`. Rewrite using `[dif_pos hf]`. Apply `norm_pos_iff.2` to reduce the goal to its premises. Introduce `h0`.

Establish `hcomp : ((Matrix.toLin' g).restrict hg).comp ((Matrix.toLin' f).restrict hf) = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨y, hy⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.mulVec_mulVec, hgf]`.

Use `congrArg LinearMap.det hcomp` as an intermediate fact. Rewrite `this` using `[LinearMap.det_comp, h0, mul_zero, LinearMap.det_id]`. Conclude with `zero_ne_one this`.
-/
theorem detOn_pos {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  have hf : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  have hg : ∀ y ∈ V, Matrix.toLin' g y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact GlobalTheory.FlagLeviGroup.inv_keeps hgf V hV y hy
  unfold detOn
  rw [dif_pos hf]
  apply norm_pos_iff.2
  intro h0
  have hcomp : ((Matrix.toLin' g).restrict hg).comp ((Matrix.toLin' f).restrict hf) =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, hy⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hgf]
  have := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, h0, mul_zero, LinearMap.det_id] at this
  exact zero_ne_one this

def killing (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (V : Submodule ℂ (Fin n → ℂ)) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) := N ⊓ homSub V ⊤

/- English proof (translation)
Simplify using `[killing, Submodule.mem_inf, mem_homSub]`.
-/
theorem mem_killing {N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)} {V : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ killing N V ↔ X ∈ N ∧ ∀ y ∈ V, X *ᵥ y = 0 := by
  simp [killing, Submodule.mem_inf, mem_homSub]

section Flag

variable {r : ℕ} {F : ℕ → Submodule ℂ (Fin n → ℂ)} {N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)}

/- English proof (translation)
Introduce `X hX`. Rewrite `hX` using `[mem_homSub]`. Rewrite using `[hN]`. Introduce `s hs y hy`. Break down `Nat.lt_or_ge s k with h | h` into its components or cases.

Rewrite using `[hX.1 y (hF (Nat.succ_le_of_lt h) hy)]`. Conclude with `(F s).zero_mem`. Conclude with `hF h (hX.2 y)`.
-/
theorem homSub_le (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) (k : ℕ) :
    homSub (F k) (F k) ≤ N := by
  intro X hX
  rw [mem_homSub] at hX
  rw [hN]
  intro s hs y hy
  rcases Nat.lt_or_ge s k with h | h
  · rw [hX.1 y (hF (Nat.succ_le_of_lt h) hy)]
    exact (F s).zero_mem
  · exact hF h (hX.2 y)

/- English proof (translation)
Establish `hkk : F k ≤ F (k + 1)` using `hF (Nat.le_succ k)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `X hX`. Rewrite `hX` using `[mem_killing]`. Establish `hXN` using `(hN X).1 hX.1 k hk`.

Take `⟨p, hp⟩` from `LinearMap.exists_leftInverse_of_injective (F (k + 1)).subtype (Submodule.ker_subtype _)`. Establish `hpy : ∀ y ∈ F (k + 1), ((p y : F (k + 1)) : Fin n → ℂ) = y`. Introduce `y hy`. Simplify using `using congrArg Subtype.val (LinearMap.congr_fun hp ⟨y, hy⟩)`. Set `M : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' ((Matrix.toLin' X).comp ((F (k + 1)).subtype.comp p))`.

Establish `hM : ∀ y, M *ᵥ y = X *ᵥ ((p y : F (k + 1)) : Fin n → ℂ)`. Introduce `y`. Simplify using `[M, LinearMap.toMatrix'_mulVec]`. Establish `h2 : M ∈ homSub (F k) (F k)`. Rewrite using `[mem_homSub]`.

Use `⟨fun y hy => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hM, hpy y (hkk hy)]`. Conclude with `hX.2 y hy`. Rewrite using `[hM]`. Conclude with `hXN _ (p y).2`.

Establish `h1 : X - M ∈ killing N (F (k + 1))`. Rewrite using `[mem_killing]`. Use `⟨N.sub_mem hX.1 (homSub_le hF hN k h2), fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, hM, hpy y hy, sub_self]`. Use `Submodule.add_mem_sup h1 h2` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Apply `sup_le` to reduce the goal to its premises. Introduce `X hX`. Rewrite `hX`, the goal using `[mem_killing]`. Conclude with `⟨hX.1, fun y hy => hX.2 y (hkk hy)⟩`.

Introduce `X hX`. Rewrite using `[mem_killing]`. Use `⟨homSub_le hF hN k hX, ?_⟩` and prove the remaining obligations. Rewrite `hX` using `[mem_homSub]`. Conclude with `hX.1`.
-/
theorem killing_eq_sup (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) {k : ℕ} (hk : k < r) :
    killing N (F k) = killing N (F (k + 1)) ⊔ homSub (F k) (F k) := by
  have hkk : F k ≤ F (k + 1) := hF (Nat.le_succ k)
  apply le_antisymm
  · intro X hX
    rw [mem_killing] at hX
    have hXN := (hN X).1 hX.1 k hk
    obtain ⟨p, hp⟩ :=
      LinearMap.exists_leftInverse_of_injective (F (k + 1)).subtype (Submodule.ker_subtype _)
    have hpy : ∀ y ∈ F (k + 1), ((p y : F (k + 1)) : Fin n → ℂ) = y := by
      intro y hy
      simpa using congrArg Subtype.val (LinearMap.congr_fun hp ⟨y, hy⟩)
    let M : Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toMatrix' ((Matrix.toLin' X).comp ((F (k + 1)).subtype.comp p))
    have hM : ∀ y, M *ᵥ y = X *ᵥ ((p y : F (k + 1)) : Fin n → ℂ) := by
      intro y
      simp [M, LinearMap.toMatrix'_mulVec]
    have h2 : M ∈ homSub (F k) (F k) := by
      rw [mem_homSub]
      refine ⟨fun y hy => ?_, fun y => ?_⟩
      · rw [hM, hpy y (hkk hy)]
        exact hX.2 y hy
      · rw [hM]
        exact hXN _ (p y).2
    have h1 : X - M ∈ killing N (F (k + 1)) := by
      rw [mem_killing]
      refine ⟨N.sub_mem hX.1 (homSub_le hF hN k h2), fun y hy => ?_⟩
      rw [Matrix.sub_mulVec, hM, hpy y hy, sub_self]
    have := Submodule.add_mem_sup h1 h2
    rwa [sub_add_cancel] at this
  · apply sup_le
    · intro X hX
      rw [mem_killing] at hX ⊢
      exact ⟨hX.1, fun y hy => hX.2 y (hkk hy)⟩
    · intro X hX
      rw [mem_killing]
      refine ⟨homSub_le hF hN k hX, ?_⟩
      rw [mem_homSub] at hX
      exact hX.1

/- English proof (translation)
Establish `hkk : F k ≤ F (k + 1)` using `hF (Nat.le_succ k)`. Use extensionality with `X`. Rewrite using `[Submodule.mem_inf, mem_killing, mem_homSub, mem_homSub]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Establish `h3 : X ∈ homSub (F k) (F k)`. Rewrite using `[mem_homSub]`. Conclude with `⟨fun y hy => h1 y (hkk hy), h2⟩`. Conclude with `⟨⟨homSub_le hF hN k h3, h1⟩, fun y hy => h1 y (hkk hy), h2⟩`. Introduce and unpack `⟨⟨_, h1⟩, _, h2⟩`.

Conclude with `⟨h1, h2⟩`.
-/
theorem homSub_eq_inf (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) (k : ℕ) :
    homSub (F (k + 1)) (F k) = killing N (F (k + 1)) ⊓ homSub (F k) (F k) := by
  have hkk : F k ≤ F (k + 1) := hF (Nat.le_succ k)
  ext X
  rw [Submodule.mem_inf, mem_killing, mem_homSub, mem_homSub]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : X ∈ homSub (F k) (F k) := by
      rw [mem_homSub]
      exact ⟨fun y hy => h1 y (hkk hy), h2⟩
    exact ⟨⟨homSub_le hF hN k h3, h1⟩, fun y hy => h1 y (hkk hy), h2⟩
  · rintro ⟨⟨_, h1⟩, _, h2⟩
    exact ⟨h1, h2⟩

end Flag

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r), Finset.sum_range_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem telescope_nat (a c : ℕ → ℕ) (r : ℕ) (h : ∀ k < r, a k = a (k + 1) + c k) :
    a 0 = a r + ∑ s ∈ Finset.range r, c s := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r),
      Finset.sum_range_succ]
    ring

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r), Finset.prod_range_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem telescope_real (a c : ℕ → ℝ) (r : ℕ) (h : ∀ k < r, a k = a (k + 1) * c k) :
    a 0 = a r * ∏ s ∈ Finset.range r, c s := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r),
      Finset.prod_range_succ]
    ring

/- English proof (translation)
Introduce `n f g r F N hfg hdet hF h0 hr hfF hN`. Establish `hgf : g * f = 1` using `mul_eq_one_comm.mp hfg`. Establish `hgF : ∀ s, ∀ y ∈ F s, g *ᵥ y ∈ F s` using `fun s => GlobalTheory.FlagLeviGroup.inv_keeps hgf (F s) (hfF s)`. Establish `hNst : ∀ X ∈ N, twoSided f g X ∈ N`. Introduce `X hX`.

Rewrite `hX`, the goal using `[hN]`. Introduce `s hs y hy`. Rewrite using `[twoSided_mulVec]`. Conclude with `hfF s _ (hX s hs _ (hgF (s + 1) y hy))`. Establish `hKst : ∀ k, ∀ X ∈ killing N (F k), twoSided f g X ∈ killing N (F k)`.

Introduce `k X hX`. Rewrite `hX`, the goal using `[mem_killing]`. Use `⟨hNst X hX.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[twoSided_mulVec, hX.2 _ (hgF k y hy), Matrix.mulVec_zero]`. Establish `hHst : ∀ P Q : Submodule ℂ (Fin n → ℂ), (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → ∀ X ∈ homSub P Q, twoSided f g X ∈ homSub P Q` using `fun P Q hP hQ => homSub_stable (GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP) hQ`.

Establish `key` using `fun (P Q : Submodule ℂ (Fin n → ℂ)) (hP : ∀ y ∈ P, f *ᵥ y ∈ P) (hQ : ∀ y ∈ Q, f *ᵥ y ∈ Q) => GlobalTheory.T.det_conj_on_matrices_killing_into_subspace n f g P Q (homSub P Q) hfg hdet hP hQ (fun _ => mem_homSub)`. Establish `hmono : ∀ k, F k ≤ F (k + 1)` using `fun k => hF (Nat.le_succ k)`. Establish `hK0 : killing N (F 0) = N`. Use extensionality with `X`. Rewrite using `[mem_killing, h0]`.

Simplify using the standard rewrite rules. Establish `hKr : killing N (F r) = ⊥`. Use extensionality with `X`. Rewrite using `[mem_killing, hr, Submodule.mem_bot]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, h⟩`. Establish `hX : Matrix.toLin' X = 0` using `LinearMap.ext fun y => by`. Simplify using `using h y Submodule.mem_top`. Conclude with `(LinearEquiv.map_eq_zero_iff Matrix.toLin').1 hX`. Introduce and unpack `rfl`.

Conclude with `⟨N.zero_mem, fun y _ => Matrix.zero_mulVec y⟩`. Establish `hdim : ∀ k < r, Module.finrank ℂ (killing N (F k)) = Module.finrank ℂ (killing N (F (k + 1))) + (Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k)) * Module.finrank ℂ (F k)`. Introduce `k hk`. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (killing N (F (k + 1))) (homSub (F k) (F k))`. Rewrite `h1` using `[← killing_eq_sup hF hN hk, ← homSub_eq_inf hF hN k, (key _ _ (hfF (k + 1)) (hfF k)).1, (key _ _ (hfF k) (hfF k)).1]`.

Establish `hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1))` using `Submodule.finrank_mono (hmono k)`. Establish `hle2 : Module.finrank ℂ (F (k + 1)) ≤ n`. Simplify using `using Submodule.finrank_le (F (k + 1))`. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hle1`. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le hle2`.

Establish `E1 : n - Module.finrank ℂ (F (k + 1)) = m` using `by omega`. Establish `E2 : n - Module.finrank ℂ (F k) = m + e` using `by omega`. Establish `E3 : Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k) = e` using `by omega`. Rewrite `h1` using `[E1, E2]`. Rewrite using `[E3]`.

Rewrite `h1` using `[add_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstep : ∀ k < r, ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖ = ‖LinearMap.det ((twoSided f g).restrict (hKst (k + 1)))‖ * (detOn f (F k) ^ Module.finrank ℂ (F (k + 1)) / detOn f (F (k + 1)) ^ Module.finrank ℂ (F k))`. Introduce `k hk`. Establish `hm` using `det_sup_mul_det_inf (twoSided f g) (killing N (F (k + 1))) (homSub (F k) (F k)) (killing N (F k)) (homSub (F (k + 1)) (F k)) (killing_eq_sup hF hN hk) (homSub_eq_inf hF hN k) (hKst (k + 1)) (hHst _ _ (hfF k) (hfF k)) (hKst k) (hHst _ _ (hfF (k + 1)) (hfF k))`.

Establish `hA` using `(key _ _ (hfF (k + 1)) (hfF k)).2 ((twoSided f g).restrict (hHst _ _ (hfF (k + 1)) (hfF k))) (fun X => twoSided_apply f g _)`. Establish `hB` using `(key _ _ (hfF k) (hfF k)).2 ((twoSided f g).restrict (hHst _ _ (hfF k) (hfF k))) (fun X => twoSided_apply f g _)`. Establish `hnorm` using `congrArg (fun z : ℂ => ‖z‖) hm`. Simplify using `only [norm_mul] at hnorm`. Rewrite `hnorm` using `[hA, hB]`.

Establish `hx` using `detOn_pos hgf (F k) (hfF k)`. Establish `hy` using `detOn_pos hgf (F (k + 1)) (hfF (k + 1))`. Establish `hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1))` using `Submodule.finrank_mono (hmono k)`. Establish `hle2 : Module.finrank ℂ (F (k + 1)) ≤ n`. Simplify using `using Submodule.finrank_le (F (k + 1))`.

Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hle1`. Take `⟨m, hm'⟩` from `Nat.exists_eq_add_of_le hle2`. Establish `E1 : n - Module.finrank ℂ (F (k + 1)) = m` using `by omega`. Establish `E2 : n - Module.finrank ℂ (F k) = m + e` using `by omega`. Rewrite `hnorm` using `[E1, E2]`.

Rewrite using `[he, mul_div_assoc', eq_div_iff (pow_pos hy _).ne']`. Apply `mul_left_cancel₀ (pow_ne_zero m hx.ne')` to reduce the goal to its premises. Take the linear combination `hnorm`. Establish `hDr : ‖LinearMap.det ((twoSided f g).restrict (hKst r))‖ = 1`. Establish `hb : ∀ X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), twoSided f g X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))`.

Introduce `X hX`. Rewrite `hX`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hX, map_zero]`. Use `det_eq_of_intertwine (LinearEquiv.ofEq _ _ hKr) ((twoSided f g).restrict (hKst r)) ((twoSided f g).restrict hb) (fun x => Subtype.ext rfl)` as an intermediate fact. Rewrite using `[← this, LinearMap.det_eq_one_of_subsingleton, norm_one]`.

Use `⟨?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `ht` using `telescope_nat (fun k => Module.finrank ℂ (killing N (F k))) (fun s => (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s)) r hdim`. Rewrite `ht` using `[hK0, hKr, finrank_bot, zero_add]`. Conclude with `ht`. Establish `ht` using `telescope_real (fun k => ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖) (fun s => detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) / detOn f (F (s + 1)) ^ Module.finrank ℂ (F s)) r hstep`.

Rewrite `ht` using `[hDr, one_mul]`. Rewrite using `[← ht]`. Use `det_eq_of_intertwine (LinearEquiv.ofEq _ _ hK0) ((twoSided f g).restrict (hKst 0)) φ (fun x => Subtype.ext (by rw [hφ]; exact twoSided_apply f g _))` as an intermediate fact. Rewrite using `[this]`.
-/
theorem flag_finrank_det : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) (F : ℕ → Submodule ℂ (Fin n → ℂ)) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → Monotone F → F 0 = ⊥ → F r = ⊤ → (∀ s, ∀ y ∈ F s, f *ᵥ y ∈ F s) → (∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) → Module.finrank ℂ N = ∑ s ∈ Finset.range r, (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s) ∧ ∀ φ : N →ₗ[ℂ] N, (∀ X : N, ((φ X : N) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = ∏ s ∈ Finset.range r, detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) / detOn f (F (s + 1)) ^ Module.finrank ℂ (F s) := by
  intro n f g r F N hfg hdet hF h0 hr hfF hN
  have hgf : g * f = 1 := mul_eq_one_comm.mp hfg
  have hgF : ∀ s, ∀ y ∈ F s, g *ᵥ y ∈ F s := fun s =>
    GlobalTheory.FlagLeviGroup.inv_keeps hgf (F s) (hfF s)
  have hNst : ∀ X ∈ N, twoSided f g X ∈ N := by
    intro X hX
    rw [hN] at hX ⊢
    intro s hs y hy
    rw [twoSided_mulVec]
    exact hfF s _ (hX s hs _ (hgF (s + 1) y hy))
  have hKst : ∀ k, ∀ X ∈ killing N (F k), twoSided f g X ∈ killing N (F k) := by
    intro k X hX
    rw [mem_killing] at hX ⊢
    refine ⟨hNst X hX.1, fun y hy => ?_⟩
    rw [twoSided_mulVec, hX.2 _ (hgF k y hy), Matrix.mulVec_zero]
  have hHst : ∀ P Q : Submodule ℂ (Fin n → ℂ), (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) →
      ∀ X ∈ homSub P Q, twoSided f g X ∈ homSub P Q := fun P Q hP hQ =>
    homSub_stable (GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP) hQ
  have key := fun (P Q : Submodule ℂ (Fin n → ℂ)) (hP : ∀ y ∈ P, f *ᵥ y ∈ P)
      (hQ : ∀ y ∈ Q, f *ᵥ y ∈ Q) =>
    GlobalTheory.T.det_conj_on_matrices_killing_into_subspace n f g P Q (homSub P Q) hfg hdet hP hQ (fun _ => mem_homSub)
  have hmono : ∀ k, F k ≤ F (k + 1) := fun k => hF (Nat.le_succ k)
  have hK0 : killing N (F 0) = N := by
    ext X
    rw [mem_killing, h0]
    simp
  have hKr : killing N (F r) = ⊥ := by
    ext X
    rw [mem_killing, hr, Submodule.mem_bot]
    constructor
    · rintro ⟨_, h⟩
      have hX : Matrix.toLin' X = 0 := LinearMap.ext fun y => by
        simpa using h y Submodule.mem_top
      exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').1 hX
    · rintro rfl
      exact ⟨N.zero_mem, fun y _ => Matrix.zero_mulVec y⟩
  have hdim : ∀ k < r, Module.finrank ℂ (killing N (F k)) =
      Module.finrank ℂ (killing N (F (k + 1))) +
        (Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k)) * Module.finrank ℂ (F k) := by
    intro k hk
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (killing N (F (k + 1))) (homSub (F k) (F k))
    rw [← killing_eq_sup hF hN hk, ← homSub_eq_inf hF hN k, (key _ _ (hfF (k + 1)) (hfF k)).1,
      (key _ _ (hfF k) (hfF k)).1] at h1
    have hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1)) :=
      Submodule.finrank_mono (hmono k)
    have hle2 : Module.finrank ℂ (F (k + 1)) ≤ n := by
      simpa using Submodule.finrank_le (F (k + 1))
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle1
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle2
    have E1 : n - Module.finrank ℂ (F (k + 1)) = m := by omega
    have E2 : n - Module.finrank ℂ (F k) = m + e := by omega
    have E3 : Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k) = e := by omega
    rw [E1, E2] at h1
    rw [E3]
    rw [add_mul] at h1
    linarith
  have hstep : ∀ k < r, ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖ =
      ‖LinearMap.det ((twoSided f g).restrict (hKst (k + 1)))‖ *
        (detOn f (F k) ^ Module.finrank ℂ (F (k + 1)) /
          detOn f (F (k + 1)) ^ Module.finrank ℂ (F k)) := by
    intro k hk
    have hm := det_sup_mul_det_inf (twoSided f g) (killing N (F (k + 1))) (homSub (F k) (F k))
      (killing N (F k)) (homSub (F (k + 1)) (F k)) (killing_eq_sup hF hN hk)
      (homSub_eq_inf hF hN k) (hKst (k + 1)) (hHst _ _ (hfF k) (hfF k)) (hKst k)
      (hHst _ _ (hfF (k + 1)) (hfF k))
    have hA := (key _ _ (hfF (k + 1)) (hfF k)).2
      ((twoSided f g).restrict (hHst _ _ (hfF (k + 1)) (hfF k))) (fun X => twoSided_apply f g _)
    have hB := (key _ _ (hfF k) (hfF k)).2
      ((twoSided f g).restrict (hHst _ _ (hfF k) (hfF k))) (fun X => twoSided_apply f g _)
    have hnorm := congrArg (fun z : ℂ => ‖z‖) hm
    simp only [norm_mul] at hnorm
    rw [hA, hB] at hnorm
    have hx := detOn_pos hgf (F k) (hfF k)
    have hy := detOn_pos hgf (F (k + 1)) (hfF (k + 1))
    have hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1)) :=
      Submodule.finrank_mono (hmono k)
    have hle2 : Module.finrank ℂ (F (k + 1)) ≤ n := by
      simpa using Submodule.finrank_le (F (k + 1))
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle1
    obtain ⟨m, hm'⟩ := Nat.exists_eq_add_of_le hle2
    have E1 : n - Module.finrank ℂ (F (k + 1)) = m := by omega
    have E2 : n - Module.finrank ℂ (F k) = m + e := by omega
    rw [E1, E2] at hnorm
    rw [he, mul_div_assoc', eq_div_iff (pow_pos hy _).ne']
    apply mul_left_cancel₀ (pow_ne_zero m hx.ne')
    linear_combination hnorm
  have hDr : ‖LinearMap.det ((twoSided f g).restrict (hKst r))‖ = 1 := by
    have hb : ∀ X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)),
        twoSided f g X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) := by
      intro X hX
      rw [Submodule.mem_bot] at hX ⊢
      rw [hX, map_zero]
    have := det_eq_of_intertwine (LinearEquiv.ofEq _ _ hKr) ((twoSided f g).restrict (hKst r))
      ((twoSided f g).restrict hb) (fun x => Subtype.ext rfl)
    rw [← this, LinearMap.det_eq_one_of_subsingleton, norm_one]
  refine ⟨?_, fun φ hφ => ?_⟩
  · have ht := telescope_nat (fun k => Module.finrank ℂ (killing N (F k)))
      (fun s => (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s))
      r hdim
    rw [hK0, hKr, finrank_bot, zero_add] at ht
    exact ht
  · have ht := telescope_real (fun k => ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖)
      (fun s => detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) /
        detOn f (F (s + 1)) ^ Module.finrank ℂ (F s)) r hstep
    rw [hDr, one_mul] at ht
    rw [← ht]
    have := det_eq_of_intertwine (LinearEquiv.ofEq _ _ hK0) ((twoSided f g).restrict (hKst 0)) φ
      (fun x => Subtype.ext (by rw [hφ]; exact twoSided_apply f g _))
    rw [this]

end GlobalTheory.FlagModulus
