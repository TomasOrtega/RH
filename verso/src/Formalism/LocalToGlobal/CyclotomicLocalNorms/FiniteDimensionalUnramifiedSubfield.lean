import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.FiniteDimensionalQ0

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `inf_le_right`.
-/
theorem unramified_subfield_le_maxUnramified (K : FinExt l) : K0 K ≤ MaximalUnramifiedExtension l := inf_le_right

instance finiteDimensional_unramified_subfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

instance normal_unramified_subfield (K : FinExt l) : Normal ℚ_[l] ↥(K0 K) :=
  normal_of_le_Kur (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K)

instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩

def σE (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := (FrobQ l).restrictNormal ↥(K0 K)

def σ (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) := (σE K : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem σ_apply (K : FinExt l) (x : ↥(K0 K)) : σ K x = σE K x := rfl

/- English proof (translation)
The claim follows from `(σE K).bijective`.
-/
theorem σ_bij (K : FinExt l) : Function.Bijective (σ K) := (σE K).bijective

/- English proof (translation)
Establish `h : σE K ^ i = (FrobQ l ^ i).restrictNormal ↥(K0 K)` using `(map_pow (AlgEquiv.restrictNormalHom (K₁ := Om l) ↥(K0 K)) (FrobQ l) i).symm`. Rewrite using `[h]`. Conclude with `AlgEquiv.restrictNormal_commutes (FrobQ l ^ i) ↥(K0 K) x`.
-/
theorem σE_pow_coe (K : FinExt l) (i : ℕ) (x : ↥(K0 K)) :
    (((σE K ^ i) x : ↥(K0 K)) : Om l) = (FrobQ l ^ i) (x : Om l) := by
  have h : σE K ^ i = (FrobQ l ^ i).restrictNormal ↥(K0 K) :=
    (map_pow (AlgEquiv.restrictNormalHom (K₁ := Om l) ↥(K0 K)) (FrobQ l) i).symm
  rw [h]
  exact AlgEquiv.restrictNormal_commutes (FrobQ l ^ i) ↥(K0 K) x

/- English proof (translation)
Use `σE_pow_coe K 1 x` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Then use the resulting hypothesis.
-/
theorem σ_coe (K : FinExt l) (x : ↥(K0 K)) : ((σ K x : ↥(K0 K)) : Om l) = FrobQ l (x : Om l) := by
  have := σE_pow_coe K 1 x
  rwa [pow_one, pow_one] at this

/- English proof (translation)
Rewrite using `[σ_coe]`. Conclude with `FrobQ_spec _ hx`.
-/
theorem PD_σ (K : FinExt l) (x : ↥(K0 K)) (hx : ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1) :
    ‖(((σ K x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1 := by
  rw [σ_coe]
  exact FrobQ_spec _ hx

/- English proof (translation)
Rewrite using `[← pow_fixes_iff (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) i]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Use `σE_pow_coe K i ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `this.symm`. Introduce `h`. Use extensionality with `x`. Rewrite using `[σE_pow_coe]`. Conclude with `h x x.2`.
-/
theorem σE_pow_eq_one_iff (K : FinExt l) (i : ℕ) :
    σE K ^ i = 1 ↔ Module.finrank ℚ_[l] ↥(K0 K) ∣ i := by
  rw [← pow_fixes_iff (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) i]
  constructor
  · intro h x hx
    have := σE_pow_coe K i ⟨x, hx⟩
    rw [h] at this
    exact this.symm
  · intro h
    ext x
    rw [σE_pow_coe]
    exact h x x.2

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Conclude with `orderOf_dvd_of_pow_eq_one ((σE_pow_eq_one_iff K _).2 dvd_rfl)`. Conclude with `(σE_pow_eq_one_iff K _).1 (pow_orderOf_eq_one _)`.
-/
theorem orderOf_σE (K : FinExt l) : orderOf (σE K) = Module.finrank ℚ_[l] ↥(K0 K) := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((σE_pow_eq_one_iff K _).2 dvd_rfl)
  · exact (σE_pow_eq_one_iff K _).1 (pow_orderOf_eq_one _)

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_GQ_of_algHom τ`. Take `⟨i, hi, h⟩` from `exists_pow_of_GQ (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g`. Conclude with `⟨i, hi, fun x => by rw [← hg, σE_pow_coe, h x x.2]⟩`.
-/
theorem exists_pow_σE (K : FinExt l) (τ : ↥(K0 K) →ₐ[ℚ_[l]] Om l) :
    ∃ i < Module.finrank ℚ_[l] ↥(K0 K), ∀ x, τ x = (((σE K ^ i) x : ↥(K0 K)) : Om l) := by
  obtain ⟨g, hg⟩ := exists_GQ_of_algHom τ
  obtain ⟨i, hi, h⟩ := exists_pow_of_GQ (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g
  exact ⟨i, hi, fun x => by rw [← hg, σE_pow_coe, h x x.2]⟩

/- English proof (translation)
Establish `h1 : FrobQ l (x : Om l) = x` using `by rw [← σ_coe, h]`. Take `⟨a, ha⟩` from `IntermediateField.mem_bot.1 (mem_bot_of_FrobQ_fixed (unramified_subfield_le_maxUnramified K x.2) h1)`. Conclude with `⟨a, Subtype.ext ha⟩`.
-/
theorem σ_fixed (K : FinExt l) (x : ↥(K0 K)) (h : σ K x = x) :
    ∃ a : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) a = x := by
  have h1 : FrobQ l (x : Om l) = x := by rw [← σ_coe, h]
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 (mem_bot_of_FrobQ_fixed (unramified_subfield_le_maxUnramified K x.2) h1)
  exact ⟨a, Subtype.ext ha⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_GQ_of_algHom ((K0 K).val.comp τ)`. Establish `h1 : ∀ y ∈ K0 K, ‖y‖ ≤ 1 → ‖g y - y ^ l‖ < 1`. Introduce `y hy hy1`. Use `hτ ⟨y, hy⟩ hy1` as an intermediate fact. Establish `h2 : g y = ((τ ⟨y, hy⟩ : ↥(K0 K)) : Om l)` using `hg ⟨y, hy⟩`.

Rewrite using `[h2]`. Conclude with `this`. Use extensionality with `x`. Rewrite using `[σ_coe, ← eq_FrobQ_of_congr (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g h1 x.2]`. Conclude with `(hg x).symm`.
-/
theorem eq_σ_of_congr (K : FinExt l) (τ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))
    (hτ : ∀ x : ↥(K0 K), ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1 →
      ‖(((τ x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1) : τ = σ K := by
  obtain ⟨g, hg⟩ := exists_GQ_of_algHom ((K0 K).val.comp τ)
  have h1 : ∀ y ∈ K0 K, ‖y‖ ≤ 1 → ‖g y - y ^ l‖ < 1 := by
    intro y hy hy1
    have := hτ ⟨y, hy⟩ hy1
    have h2 : g y = ((τ ⟨y, hy⟩ : ↥(K0 K)) : Om l) := hg ⟨y, hy⟩
    rw [h2]
    exact this
  ext x
  rw [σ_coe, ← eq_FrobQ_of_congr (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g h1 x.2]
  exact (hg x).symm

def emb {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  (IntermediateField.inclusion hle).comp ((σE K ^ (-i).val : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K)) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_coe {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (x : ↥(K0 K)) : ((emb hle i x : ↥LL.1) : Om l) = (((σE K ^ (-i).val) x : ↥(K0 K)) : Om l) := rfl

/- English proof (translation)
Rewrite using `[pow_eq_pow_iff_modEq, orderOf_σE]`. Conclude with `(ZMod.natCast_eq_natCast_iff a b _).1 h`.
-/
theorem σE_pow_val_eq {K : FinExt l} {a b : ℕ}
    (h : (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) = (b : ZMod _)) : σE K ^ a = σE K ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_σE]
  exact (ZMod.natCast_eq_natCast_iff a b _).1 h

/- English proof (translation)
Substitute `hτ` using the available equality. Establish `h : σE K ^ (-(i + 1)).val * σE K = σE K ^ (-i).val`. Rewrite using `[← pow_succ]`. Apply `σE_pow_val_eq` to reduce the goal to its premises. Use `push_cast`.

Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `x`. Rewrite using `[AlgHom.comp_apply, emb_coe, emb_coe, ← h]`. Both sides reduce to the same expression.
-/
theorem emb_σ {K LL : FinExt l} (hle : K0 K ≤ LL.1) (τ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K)) (hτ : τ = σ K)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) : (emb hle (i + 1)).comp τ = emb hle i := by
  subst hτ
  have h : σE K ^ (-(i + 1)).val * σE K = σE K ^ (-i).val := by
    rw [← pow_succ]
    apply σE_pow_val_eq
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  ext x
  rw [AlgHom.comp_apply, emb_coe, emb_coe, ← h]
  rfl

end Formalism.L2.LocGap.Gal
