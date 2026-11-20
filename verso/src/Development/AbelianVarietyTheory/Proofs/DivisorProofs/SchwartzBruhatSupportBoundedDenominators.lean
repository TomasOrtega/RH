import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]`.
-/
theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)`.
-/
theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

/- English proof (translation)
Establish `hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F)`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih => simp [Nat.cast_succ, ih]`. Simplify using `[hm]`.
-/
theorem natCast_mul_apply (m : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((m : FiniteAdeleRing (𝓞 F) F) * a) v = (m : v.adicCompletion F) * a v := by
  have hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F) := by
    induction m with
    | zero => simp
    | succ n ih => simp [Nat.cast_succ, ih]
  simp [hm]

/- English proof (translation)
Establish `h : denSet (F` using `F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by`. Use extensionality with `y`. Simplify using `only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply, norm_le_one_iff_mem]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))`.
-/
theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

/- English proof (translation)
Take `⟨k, rfl⟩` from `hd`. Rewrite using `[Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]`. Conclude with `mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz`.
-/
theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz

/- English proof (translation)
Introduce `_ hy i v` and use `norm_mul_le_one_of_dvd hd (hy i v)`.
-/
theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

/- English proof (translation)
Establish `hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite`. Apply `(Filter.eventually_cofinite.1 a.2).subset` to reduce the goal to its premises. Introduce `v hv`. Simplify using `only [Function.mem_mulSupport] at hv`. Introduce `hmem`.

Apply `hv` to reduce the goal to its premises. Establish `: ‖a v‖ ≤ 1` using `(norm_le_one_iff_mem v _).2 hmem`. Conclude with `max_eq_left (by exact_mod_cast this)`. Take `⟨d, hd, -, h⟩` from `GlobalTheory.SmoothForms.denom_global (F := F) (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf`. Conclude with `⟨d, hd, fun v => h v _ (le_max_right _ _)⟩`.
-/
theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

/- English proof (translation)
Use `choose d hd h using fun i => exists_denom (y i)`. Conclude with `⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v => norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩`.
-/
theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

/- English proof (translation)
Establish `hK : IsCompact (tsupport g)` using `hg.2`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1)) (fun n => isOpen_denSet κ _) (fun y _ => by`. Take `⟨m, hm, hy⟩` from `exists_mem_denSet κ y`. Take `⟨n, rfl⟩` from `Nat.exists_eq_add_of_lt hm`. Conclude with `Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)`.

Use `⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩` and prove the remaining obligations. Establish `hy : (fun i => (x i).2) ∈ tsupport g` using `subset_tsupport _ hx`. Take `⟨n, hn, hyn⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Conclude with `denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v`.
-/
theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
