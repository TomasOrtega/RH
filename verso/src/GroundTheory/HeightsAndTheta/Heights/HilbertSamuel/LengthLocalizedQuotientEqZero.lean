import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WeightedHomogeneousSubmoduleBlockWeightIntEqRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Length

variable {R : Type*} [CommRing R]

/- English proof (translation)
The claim follows from `| 0, f, c, _ => by simp | n + 1, f, c, h => by have ih : f (Fin.succ 0) = ∑ j : Fin n, c j.succ + f (Fin.last n).succ := telescope_enat n (fun k => f k.succ) (fun j => c j.succ) (fun j => h j.succ) calc f 0 = c 0 + f (Fin.succ 0) := by simpa using h 0 _ = ∑ j, c j + f (Fin.last ( …`.
-/
theorem telescope_enat : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (c : Fin n → ℕ∞),
    (∀ j : Fin n, f j.castSucc = c j + f j.succ) → f 0 = ∑ j, c j + f (Fin.last n)
  | 0, f, c, _ => by simp
  | n + 1, f, c, h => by
    have ih : f (Fin.succ 0) = ∑ j : Fin n, c j.succ + f (Fin.last n).succ :=
      telescope_enat n (fun k => f k.succ) (fun j => c j.succ) (fun j => h j.succ)
    calc f 0 = c 0 + f (Fin.succ 0) := by simpa using h 0
      _ = ∑ j, c j + f (Fin.last (n + 1)) := by
        rw [ih, Fin.succ_last, Fin.sum_univ_succ, add_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m s => rw [LocalizedModule.map_mk, IsLocalizedModule.map_LocalizedModules]`.
-/
theorem localizedModule_map_coe (P : Submonoid R) {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] (f : M₀ →ₗ[R] M₁) :
    ⇑(LocalizedModule.map P f) = ⇑(IsLocalizedModule.map P (LocalizedModule.mkLinearMap P M₀)
      (LocalizedModule.mkLinearMap P M₁) f) := by
  funext y
  induction y using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, IsLocalizedModule.map_LocalizedModules]

/- English proof (translation)
Use `Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f) (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf) (LocalizedModule.map_surjective _ g hg) ?_` and prove the remaining obligations. Rewrite using `[localizedModule_map_coe, localizedModule_map_coe]`. Conclude with `LocalizedModule.map_exact p.primeCompl f g h`.
-/
theorem length_localized_eq_add (p : Ideal R) [p.IsPrime] {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₁) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₀) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₂) := by
  refine Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) ?_
  rw [localizedModule_map_coe, localizedModule_map_coe]
  exact LocalizedModule.map_exact p.primeCompl f g h

/- English proof (translation)
Take `⟨t, htq, htp⟩` from `Set.not_subset.mp h`. Establish `key : ∀ y : LocalizedModule p.primeCompl (R ⧸ q), y = 0`. Introduce `y`. Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m s`.

Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Rewrite using `[← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Use `⟨⟨t, htp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `q.mul_mem_right r htq`.

Establish `: Subsingleton (LocalizedModule p.primeCompl (R ⧸ q))` using `⟨fun a b => by rw [key a, key b]⟩`. Conclude with `Module.length_eq_zero`.
-/
theorem length_localized_quotient_eq_zero (p q : Ideal R) [p.IsPrime] (h : ¬ q ≤ p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨t, htq, htp⟩ := Set.not_subset.mp h
  have key : ∀ y : LocalizedModule p.primeCompl (R ⧸ q), y = 0 := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨⟨t, htp⟩, ?_⟩
      rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact q.mul_mem_right r htq
  have : Subsingleton (LocalizedModule p.primeCompl (R ⧸ q)) :=
    ⟨fun a b => by rw [key a, key b]⟩
  exact Module.length_eq_zero

/- English proof (translation)
Rewrite using `[Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]`. Establish `hne : ∀ (r : R) (s : p.primeCompl), LocalizedModule.mk (Ideal.Quotient.mk p r) s = 0 → r ∈ p`. Introduce `r s h`. Rewrite `h` using `[← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `h`.

Rewrite `hu` using `[one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(hp.mem_or_mem hu).resolve_left u.2`. Use `⟨⟨LocalizedModule.mk (Ideal.Quotient.mk p 1) 1, 0, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hne 1 1 h))⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx y`. Proceed by induction on `x using LocalizedModule.induction_on with`.

Consider the case `h m s`. Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m' t`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Take `⟨r', rfl⟩` from `Ideal.Quotient.mk_surjective m'`.

Establish `hr : r ∉ p` using `fun hr => hx (by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hr, LocalizedModule.zero_mk])`. Use `⟨Localization.mk (r' * s) ⟨r * t, p.primeCompl.mul_mem hr t.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem length_localized_quotient_self (p : Ideal R) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ p)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (s : p.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk p r) s = 0 → r ∈ p := by
    intro r s h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
    exact (hp.mem_or_mem hu).resolve_left u.2
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk p 1) 1, 0,
    fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hne 1 1 h))⟩, ?_⟩
  intro x hx y
  induction x using LocalizedModule.induction_on with
  | h m s =>
  induction y using LocalizedModule.induction_on with
  | h m' t =>
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hr : r ∉ p := fun hr => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, LocalizedModule.zero_mk])
  refine ⟨Localization.mk (r' * s) ⟨r * t, p.primeCompl.mul_mem hr t.2⟩, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring

/- English proof (translation)
Establish `hAB : A ≤ B` using `hB ▸ le_sup_left`. Set `f : (R ⧸ q) →ₗ[R] M ⧸ A` to `Submodule.liftQ q (A.mkQ ∘ₗ LinearMap.toSpanSingleton R M x) (by`. Introduce `s hs`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(hq s).mpr hs)`.

Set `g : M ⧸ A →ₗ[R] M ⧸ B` to `A.mapQ B LinearMap.id hAB`. Establish `hf_mk : ∀ s : R, f (Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • x)` using `fun s => rfl`. Use `length_localized_eq_add p f g ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `y hy`.

Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective q y`. Rewrite `hy` using `[LinearMap.mem_ker, hf_mk, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero q).mpr ((hq s).mp hy)`. Introduce `y`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective B y`.

Conclude with `⟨Submodule.Quotient.mk m, rfl⟩`. Introduce `y`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective A y`. Simplify using `only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, hB, Set.mem_range]`. Rewrite using `[Submodule.mem_sup]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, z, hz, rfl⟩`. Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Use `⟨Submodule.Quotient.mk s, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_mk, Submodule.Quotient.eq]`.

Simplify using `using A.neg_mem ha`. Introduce and unpack `⟨y, hy⟩`. Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective q y`. Rewrite `hy` using `[hf_mk, Submodule.Quotient.eq]`. Use `⟨m - s • x, ?_, s • x, Submodule.mem_span_singleton.mpr ⟨s, rfl⟩, sub_add_cancel _ _⟩` and prove the remaining obligations.

Simplify using `using A.neg_mem hy`.
-/
theorem length_localized_step (p : Ideal R) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (x : M) (q : Ideal R) (hB : B = A ⊔ Submodule.span R {x})
    (hq : ∀ s : R, s • x ∈ A ↔ s ∈ q) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ A)) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ B)) := by
  have hAB : A ≤ B := hB ▸ le_sup_left
  let f : (R ⧸ q) →ₗ[R] M ⧸ A := Submodule.liftQ q (A.mkQ ∘ₗ LinearMap.toSpanSingleton R M x) (by
    intro s hs
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (hq s).mpr hs)
  let g : M ⧸ A →ₗ[R] M ⧸ B := A.mapQ B LinearMap.id hAB
  have hf_mk : ∀ s : R, f (Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • x) := fun s => rfl
  refine length_localized_eq_add p f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
    rw [LinearMap.mem_ker, hf_mk, Submodule.Quotient.mk_eq_zero] at hy
    exact (Submodule.Quotient.mk_eq_zero q).mpr ((hq s).mp hy)
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective B y
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective A y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, hB,
      Set.mem_range]
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, hz, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      refine ⟨Submodule.Quotient.mk s, ?_⟩
      rw [hf_mk, Submodule.Quotient.eq]
      simpa using A.neg_mem ha
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
      rw [hf_mk, Submodule.Quotient.eq] at hy
      refine ⟨m - s • x, ?_, s • x, Submodule.mem_span_singleton.mpr ⟨s, rfl⟩, sub_add_cancel _ _⟩
      simpa using A.neg_mem hy

/- English proof (translation)
Set `L : Fin (n + 1) → ℕ∞` to `fun k => Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (M ⧸ N k))`. Establish `hstep : ∀ j : Fin n, L j.castSucc = (if q j = W then 1 else 0) + L j.succ`. Introduce `j`. Simplify using `only [L]`. Rewrite using `[length_localized_step W (N j.castSucc) (N j.succ) (x j) (q j) (hsucc j) (hann j)]`.

Use `congr 1`. Use `split_ifs with h`. Rewrite using `[h]`. Conclude with `length_localized_quotient_self W`. Apply `length_localized_quotient_eq_zero` to reduce the goal to its premises.

Introduce `hle`. Apply `h` to reduce the goal to its premises. Establish `hannq : Module.annihilator R M ≤ q j`. Introduce `s hs`. Rewrite using `[← hann j, Module.mem_annihilator.mp hs (x j)]`.

Conclude with `zero_mem _`. Conclude with `le_antisymm hle (hW.2 ⟨hprime j, hannq⟩ hle)`. Establish `h0 : L 0 = Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M)`. Simplify using `only [L]`. Rewrite using `[hN0]`.

Conclude with `(IsLocalizedModule.mapEquiv W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _) (LocalizedModule.mkLinearMap W.primeCompl M) (Localization.AtPrime W) (Submodule.quotEquivOfEqBot ⊥ rfl)).length_eq`. Establish `hl : L (Fin.last n) = 0`. Simplify using `only [L]`. Rewrite using `[hNl]`. Establish `key : ∀ y : LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M)), y = 0`.

Introduce `y`. Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m s`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).mpr Submodule.mem_top, LocalizedModule.zero_mk]`.

Establish `: Subsingleton (LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M)))` using `⟨fun a b => by rw [key a, key b]⟩`. Conclude with `Module.length_eq_zero`. Rewrite using `[← h0, telescope_enat n L _ hstep, hl, add_zero, Finset.sum_boole]`.
-/
theorem card_eq_length_of_filtration {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (hN0 : N 0 = ⊥) (hNl : N (Fin.last n) = ⊤)
    (hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j})
    (hprime : ∀ j, (q j).IsPrime) (hann : ∀ j (s : R), s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (W : Ideal R) (hW : W ∈ (Module.annihilator R M).minimalPrimes) [W.IsPrime]
    [DecidablePred fun j => q j = W] :
    (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
  let L : Fin (n + 1) → ℕ∞ := fun k =>
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (M ⧸ N k))
  have hstep : ∀ j : Fin n, L j.castSucc = (if q j = W then 1 else 0) + L j.succ := by
    intro j
    simp only [L]
    rw [length_localized_step W (N j.castSucc) (N j.succ) (x j) (q j) (hsucc j) (hann j)]
    congr 1
    split_ifs with h
    · rw [h]
      exact length_localized_quotient_self W
    · apply length_localized_quotient_eq_zero
      intro hle
      apply h
      have hannq : Module.annihilator R M ≤ q j := by
        intro s hs
        rw [← hann j, Module.mem_annihilator.mp hs (x j)]
        exact zero_mem _
      exact le_antisymm hle (hW.2 ⟨hprime j, hannq⟩ hle)
  have h0 : L 0 = Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
    simp only [L]
    rw [hN0]
    exact (IsLocalizedModule.mapEquiv W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _)
      (LocalizedModule.mkLinearMap W.primeCompl M) (Localization.AtPrime W)
      (Submodule.quotEquivOfEqBot ⊥ rfl)).length_eq
  have hl : L (Fin.last n) = 0 := by
    simp only [L]
    rw [hNl]
    have key : ∀ y : LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M)), y = 0 := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s =>
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [(Submodule.Quotient.mk_eq_zero _).mpr Submodule.mem_top, LocalizedModule.zero_mk]
    have : Subsingleton (LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M))) :=
      ⟨fun a b => by rw [key a, key b]⟩
    exact Module.length_eq_zero
  rw [← h0, telescope_enat n L _ hstep, hl, add_zero, Finset.sum_boole]

end Length

section Spans

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hi with h | h` into its components or cases.

Conclude with `Or.inr ⟨i, h, rfl⟩`. Conclude with `Or.inl (by rw [Fin.ext h])`. Introduce and unpack `(rfl | ⟨i, hi, rfl⟩)`. Conclude with `⟨j, Nat.lt_succ_self _, rfl⟩`. Conclude with `⟨i, Nat.lt_succ_of_lt hi, rfl⟩`.
-/
theorem image_val_lt_succ {α : Type*} {n : ℕ} (x : Fin n → α) (j : Fin n) :
    x '' {i | i.val < j.val + 1} = insert (x j) (x '' {i | i.val < j.val}) := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl (by rw [Fin.ext h])
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨j, Nat.lt_succ_self _, rfl⟩
    · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/- English proof (translation)
Rewrite using `[image_val_lt_succ, Submodule.span_insert, sup_comm]`.
-/
theorem span_image_val_lt_succ {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}
    (x : Fin n → M) (j : Fin n) :
    Submodule.span R (x '' {i | i.val < j.val + 1}) =
      Submodule.span R (x '' {i | i.val < j.val}) ⊔ Submodule.span R {x j} := by
  rw [image_val_lt_succ, Submodule.span_insert, sup_comm]

end Spans

/- English proof (translation)
Introduce `hA F _ K _ _ ι _ M _ _ _ _ ℳ hℳ hfin`. Use `hfin` as an intermediate fact. Take `⟨n, N, x, c, q, hN0, hNl, hj, -⟩` from `hA F K ι M ℳ ((isMultigraded_iff_isMultigrading ℳ).mp hℳ)`. Establish `hNspan : ∀ (k : ℕ) (hk : k < n + 1), N ⟨k, hk⟩ = Submodule.span (MRing ι F) (x '' {i | i.val < k})`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `hk`. Establish `h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0` using `rfl`. Rewrite using `[h0, hN0]`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `hk`. Establish `hkn : k < n` using `by omega`. Establish `hs` using `(hj ⟨k, hkn⟩).2.1`.

Establish `e1 : (⟨k, hkn⟩ : Fin n).succ = ⟨k + 1, hk⟩` using `rfl`. Establish `e2 : (⟨k, hkn⟩ : Fin n).castSucc = ⟨k, by omega⟩` using `rfl`. Rewrite `hs` using `[e1, e2]`. Rewrite using `[hs, ih (by omega)]`. Conclude with `(span_image_val_lt_succ x ⟨k, hkn⟩).symm`.

Use `⟨n, x, c, q, fun j => (hj j).1, fun j => ⟨(hj j).2.2.1, (hj j).2.2.2.1⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hNspan n (by omega)`. Establish `e : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n` using `rfl`. Rewrite `h` using `[e, hNl]`. Rewrite using `[h, ← Set.image_univ]`.

Use `congr 2`. Use extensionality with `i`. Simplify using the standard rewrite rules. Introduce `j f`. Establish `h` using `(hj j).2.2.2.2 f`.

Establish `e : j.castSucc = ⟨j.val, by omega⟩` using `rfl`. Rewrite `h` using `[e, hNspan j.val (by omega)]`. Conclude with `h`.
-/
theorem MultigradedFiltration.equiv_mp :
    GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement.{u, u} →
      MultigradedFiltration.Statement.{u} := by
  intro hA F _ K _ _ ι _ M _ _ _ _ ℳ hℳ hfin
  have := hfin
  obtain ⟨n, N, x, c, q, hN0, hNl, hj, -⟩ :=
    hA F K ι M ℳ ((isMultigraded_iff_isMultigrading ℳ).mp hℳ)
  have hNspan : ∀ (k : ℕ) (hk : k < n + 1),
      N ⟨k, hk⟩ = Submodule.span (MRing ι F) (x '' {i | i.val < k}) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, hN0]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hs := (hj ⟨k, hkn⟩).2.1
      have e1 : (⟨k, hkn⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
      have e2 : (⟨k, hkn⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
      rw [e1, e2] at hs
      rw [hs, ih (by omega)]
      exact (span_image_val_lt_succ x ⟨k, hkn⟩).symm
  refine ⟨n, x, c, q, fun j => (hj j).1, fun j => ⟨(hj j).2.2.1, (hj j).2.2.2.1⟩, ?_, ?_⟩
  · have h := hNspan n (by omega)
    have e : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [e, hNl] at h
    rw [h, ← Set.image_univ]
    congr 2
    ext i
    simp
  · intro j f
    have h := (hj j).2.2.2.2 f
    have e : j.castSucc = ⟨j.val, by omega⟩ := rfl
    rw [e, hNspan j.val (by omega)] at h
    exact h

/- English proof (translation)
Introduce `hB F _ K _ _ ι _ M _ _ _ _ _ piece hpiece`. Take `⟨n, x, c, q, hx, hq, hspan, hann⟩` from `hB F K ι M piece ((isMultigraded_iff_isMultigrading piece).mpr hpiece) inferInstance`. Set `N : Fin (n + 1) → Submodule (MRing ι F) M` to `fun k => Submodule.span (MRing ι F) (x '' {i | i.val < k.val})`. Establish `hN0 : N 0 = ⊥` using `by simp [N]`. Establish `hNl : N (Fin.last n) = ⊤`.

Simplify using `only [N, Fin.val_last]`. Rewrite using `[← hspan, ← Set.image_univ]`. Use `congr 2`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Establish `hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j}`. Introduce `j`. Simplify using `only [N, Fin.val_succ, Fin.val_castSucc]`. Conclude with `span_image_val_lt_succ x j`. Establish `hann' : ∀ j (s : MRing ι F), s • x j ∈ N j.castSucc ↔ s ∈ q j` using `fun j s => hann j s`.

Use `⟨n, N, x, c, q, hN0, hNl, fun j => ⟨hx j, hsucc j, (hq j).1, (hq j).2, hann' j⟩, ?_⟩` and prove the remaining obligations. Introduce `W hW`. Establish `: W.IsPrime` using `hW.1.1`. Use `card_eq_length_of_filtration N x q hN0 hNl hsucc (fun j => (hq j).1) hann' W hW using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
theorem MultigradedFiltration.equiv_mpr :
    MultigradedFiltration.Statement.{u} →
      GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement.{u, u} := by
  intro hB F _ K _ _ ι _ M _ _ _ _ _ piece hpiece
  obtain ⟨n, x, c, q, hx, hq, hspan, hann⟩ :=
    hB F K ι M piece ((isMultigraded_iff_isMultigrading piece).mpr hpiece) inferInstance
  let N : Fin (n + 1) → Submodule (MRing ι F) M := fun k =>
    Submodule.span (MRing ι F) (x '' {i | i.val < k.val})
  have hN0 : N 0 = ⊥ := by simp [N]
  have hNl : N (Fin.last n) = ⊤ := by
    simp only [N, Fin.val_last]
    rw [← hspan, ← Set.image_univ]
    congr 2
    ext i
    simp
  have hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} := by
    intro j
    simp only [N, Fin.val_succ, Fin.val_castSucc]
    exact span_image_val_lt_succ x j
  have hann' : ∀ j (s : MRing ι F), s • x j ∈ N j.castSucc ↔ s ∈ q j := fun j s => hann j s
  refine ⟨n, N, x, c, q, hN0, hNl, fun j => ⟨hx j, hsucc j, (hq j).1, (hq j).2, hann' j⟩, ?_⟩
  intro W hW
  have : W.IsPrime := hW.1.1
  classical
  convert card_eq_length_of_filtration N x q hN0 hNl hsucc (fun j => (hq j).1) hann' W hW using 1
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨MultigradedFiltration.equiv_mp, MultigradedFiltration.equiv_mpr⟩`.
-/
theorem MultigradedFiltration.equiv :
    GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement.{u, u} ↔
      MultigradedFiltration.Statement.{u} :=
  ⟨MultigradedFiltration.equiv_mp, MultigradedFiltration.equiv_mpr⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
